{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE EmptyDataDeriving         #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PartialTypeSignatures     #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE TypeFamilies              #-}


module Language.FGG.DeBruijn.ToNamed where


import Data.Bifunctor
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Text as T
import Language.FGG.Common
import Language.FGG.Named (Name)
import qualified Language.FGG.Named as N
import qualified Language.FGG.DeBruijn.Base as DB


-- |Convert enumerable programs to named programs.
convProg :: DB.Prog ann
         -> N.Prog
convProg (DB.FDecls _ fds) = N.Prog decls main
  where
    (decls, main) = convFDecls (emptyNS "f") fds

    convFDecls :: NS f -> DB.FDecls ann f -> ([N.Decl], N.Expr)
    convFDecls nsf (DB.NewF _ fds) = convFDecls (extendNS nsf) fds
    convFDecls nsf (DB.MDecls _ mds) = convMDecls (nsf, emptyNS "m") mds

    convMDecls :: (Ord m) => (NS f, NS m) -> DB.MDecls ann f m -> ([N.Decl], N.Expr)
    convMDecls (nsf, nsm) (DB.NewM _ mds) = convMDecls (nsf, extendNS nsm) mds
    convMDecls (nsf, nsm) (DB.TyDecls _ tys) = convTyDecls (M.empty, emptyNS "ts", emptyNS "ti", nsf, nsm) tys


-- |Convert enumerable type declarations to a list of declarations and the body of the main function.
convTyDecls :: (Ord ts, Ord m)
            => (Map (ts, m) N.Sig, NS ts, NS ti, NS f, NS m)
            -> DB.TyDecls ann ts ti f m
            -> ([N.Decl], N.Expr)
convTyDecls (sigs, nsts, nsti, nsf, nsm) (DB.LetStruct _ parBnds fldNamesAndTys rest)
  = (decl' : decls', main')
  where
    nsa'  = freshNS "a" (vlength parBnds)
    sigs' = M.mapKeysMonotonic (bimap FS id) sigs
    nsts' = extendNS nsts
    nss'  = (sigs', nsts', nsti, nsf, nsm)

    (decls', main') = convTyDecls nss' rest

    decl' = N.LetStruct (nameOf nsts' FZ) parBnds' fldNamesAndTys'
      where
        parBnds'        = [ (nameOf nsa' a, convType (undefined, nsts, nsti) parBnd)
                          | (a, parBnd) <- convVec parBnds ]
        fldNamesAndTys' = [ (nameOf nsf f, convType (nsa', nsts, nsti) fldTy)
                          | (f, fldTy) <- vlist fldNamesAndTys ]

convTyDecls (sigs, nsts, nsti, nsf, nsm) (DB.LetInterface _ parBnds parents methNamesAndSigs rest)
  = (decl' : decls', main')
  where
    nsa'  = freshNS "a" (vlength parBnds)
    nsti' = extendNS nsti
    nss'  = (sigs, nsts, nsti', nsf, nsm)

    (decls', main') = convTyDecls nss' rest

    decl' = N.LetInterface (nameOf nsti' FZ) parBnds' parents' fldNamesAndTys'
      where
        parBnds'        = [ (nameOf nsa' a, convType (undefined, nsts, nsti) parBnd)
                          | (a, parBnd) <- convVec parBnds ]
        parents'        = [ convType (nsa', nsts, nsti) parent
                          | parent <- vlist parents ]
        fldNamesAndTys' = [ convMSig (nsa', nsts, nsti', nsm) (m, methSig)
                          | (m, methSig) <- vlist methNamesAndSigs ]

convTyDecls nss (DB.TmDecls _ rest) = convTmDecls nss rest



-- |Convert enumerable term declarations to a list of declarations and the body of the main function.
convTmDecls :: (Ord ts, Ord m)
            => (Map (ts, m) N.Sig, NS ts, NS ti, NS f, NS m)
            -> DB.TmDecls ann ts ti f m
            -> ([N.Decl], N.Expr)
convTmDecls (sigs, nsts, nsti, nsf, nsm) (DB.LetMethod _ objParBnds ts m methParBnds argTys retTy body rest)
  = (decl' : rest', main')
  where
    nsa'  = freshNS "a" (vlength objParBnds)
    nsa'' = extendNS' (vlength methParBnds) nsa'
    nsx'  = extendWithNS "this" $ freshNS "x" (vlength argTys)
    sig'  = convMSig (nsa', nsts, nsti, nsm) (m, DB.MSig methParBnds (TyS ts) argTys retTy)
    sigs' = M.insert (ts, m) sig' sigs

    objParBnds' = [ (nameOf nsa' a, convType (undefined, nsts, nsti) parBnd)
                  | (a, parBnd) <- convVec objParBnds ]

    (rest', main') = convTmDecls (sigs', nsts, nsti, nsf, nsm) rest

    body' = convExpr (nsa'', nsts, nsti, nsf, nsm, nsx') body

    decl' = N.LetMethod ("this", nameOf nsts ts) objParBnds' sig' body'

convTmDecls (_, nsts, nsti, nsf, nsm) (DB.Main _ _ main) = ([], main')
  where
    main' = convExpr (emptyNS "a", nsts, nsti, nsf, nsm, emptyNS "a") main


-- |Convert enumerable expressions to named expressions.
convExpr :: (NS a, NS ts, NS ti, NS f, NS m, NS x)
         -> DB.Expr ann a ts ti f m x
         -> N.Expr
convExpr (nsa, nsts, nsti, nsf, nsm, nsx) = goEx
  where
    goTy = convType (nsa, nsts, nsti)

    goEx (DB.Var _ x)
      = N.Var (nameOf nsx x)
    goEx (DB.Struct _ ts tyArgs args)
      = N.Struct (nameOf nsts ts) (goTy <$> vlist tyArgs) (goEx . fst <$> vlist args)
    goEx (DB.Select _ str _ fld)
      = N.Select (goEx str) (nameOf nsf fld)
    goEx (DB.Call _ obj _ m tyArgs args)
      = N.Call (goEx obj) (nameOf nsm m) (goTy <$> vlist tyArgs) (goEx . fst <$> vlist args)
    goEx (DB.Assert _ e _ ty)
      = N.Assert (goEx e) (goTy ty)


-- |Convert enumerable type signatures to named type signatures.
convMSig :: (NS a, NS ts, NS ti, NS m)
         -> (m, DB.MSig a ts ti)
         -> N.Sig
convMSig (nsa, nsts, nsti, nsm) (m, DB.MSig methParBnds _ argTys retTy)
  = N.Sig m' methParBnds' argTys' retTy'
  where
    nsa'         = extendNS' (vlength methParBnds) nsa
    nsa''        = peekNS nsa (vlength methParBnds)
    nsx          = freshNS "x" (vlength argTys)
    nss          = (nsa, nsts, nsti)
    nss'         = (nsa', nsts, nsti)
    m'           = nameOf nsm m
    methParBnds' = [ (nameOf nsa'' a, convType nss parBnd) | (a, parBnd) <- convVec methParBnds ]
    argTys'      = [ (nameOf nsx  x, convType nss' argTy)  | (x, argTy)  <- convVec argTys ]
    retTy'       = convType nss' retTy


-- |Convert enumerable types to named types.
convType :: (NS a, NS ts, NS ti)
         -> DB.Type a ts ti
         -> N.Type
convType (nsa, _   , _   ) (DB.Par a)
  = N.Par (nameOf nsa a)
convType nss@(_  , nsts, nsti) (DB.Con tc tyArgs)
  = N.Con (convTyCon (nsts, nsti) tc) (vlist (vmap (convType nss) tyArgs))


-- |Convert enumerable type constructors to type names.
convTyCon :: (NS ts, NS ti) -> TyCon ts ti -> Name
convTyCon (nsts, _   ) (TyS ts) = nameOf nsts ts
convTyCon (_   , nsti) (TyI ti) = nameOf nsti ti


-- |Convert length-indexed vectors to a list of indices and values.
convVec :: Vec a n -> [(n, a)]
convVec Nil = []
convVec (Cons x xs) = (FZ, x) : [ (FS i, y) | (i, y) <- convVec xs ]



-- * Namespaces

data NS n = NS { nameOf :: n -> Name, fresh :: [Name] }

-- |Extend namespaces by binding a fresh name.
extendNS :: NS n -> NS (S n)
extendNS NS{..} = NS{ nameOf = nameOf', fresh = tail fresh }
  where
    nameOf' FZ     = head fresh
    nameOf' (FS i) = nameOf i

-- |Extend namespaces with chosen name.
extendWithNS :: Name -> NS n -> NS (S n)
extendWithNS name NS{..} = NS{ nameOf = nameOf', .. }
  where
    nameOf' FZ     = name
    nameOf' (FS i) = nameOf i

-- |Extend namespaces by binding any number of fresh names.
extendNS' :: Nat m -> NS n -> NS (m :+ n)
extendNS' Z ns = ns
extendNS' (S n) ns = extendNS (extendNS' n ns)

-- |Shrink namespace by unbinding the most recent name.
shrinkNS :: NS (S n) -> NS n
shrinkNS NS{..} = NS{ nameOf = nameOf', .. }
  where
    nameOf' i = nameOf (FS i)

-- |Empty namespace with a store of fresh names. The names are prefix0,
--  prefix1, prefix2, etc, where prefix is the first argument.
emptyNS :: Name -> NS Z
emptyNS prefix = NS { nameOf = fromZ, .. }
  where
    fresh = map ((prefix <>) . T.pack . show) [0 :: Int ..]

-- |Fresh namespace with a store of fresh names, and some number of names
--  already allocated. This is essentially |extendNS' n (emptyNS prefix)|,
--  but the Haskell type system has problems assigning that the following type.
freshNS :: Name -> Nat n -> NS n
freshNS prefix = go
  where
    go :: Nat n -> NS n
    go Z     = emptyNS prefix
    go (S n) = extendNS (go n)

-- |Singleton namespace with a store of fresh names and one specific name
--  already allocated. This is useful for, e.g., creating the namespace for
--  a method body, where we want the topmost name to be "this".
singletonNS :: Name -> Name -> NS (S Z)
singletonNS singleton prefix = NS { nameOf = nameOf', .. }
  where
    NS{..} = emptyNS prefix
    nameOf' FZ     = singleton
    nameOf' (FS i) = nameOf i

-- |Construct a namespace with only the n names that would be allocated if
--  |extendNS' n| was invoked on it, but discarding the current set of allocated
--  names. This is useful for avoiding having to implement injection and raising.
peekNS :: NS m -> Nat n -> NS n
peekNS NS{..} = go
  where
    go :: Nat n -> NS n
    go Z     = NS { nameOf = fromZ, .. }
    go (S n) = extendNS (go n)
