{-# OPTIONS -fno-warn-partial-type-signatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE RebindableSyntax          #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE PartialTypeSignatures     #-}
{-# LANGUAGE GADTs                     #-}
module Language.FGG.DeBruijn.Relevance (checkUsageProg) where


-- What counts as a usage? I would argue that what we want is:
--
--   * For each type parameter to be mentioned in a type;
--   * For each interface to be mentioned in a type;
--   * For each structure to be constructed;
--   * For each field to be mentioned in a type definition;
--   * For each method to be called;
--   * For each variable to be used.


import Prelude hiding (Monad((>>=), (>>), return, fail))
import Control.Monad.Indexed (IxPointed(ireturn), IxMonad(ibind))
import Control.Monad.Indexed.State (IxMonadState, iget, iput, runIxState)
import Data.Bool (bool)
import Data.Set (Set, (\\))
import qualified Data.Set as S
import Language.FGG.Common
import Language.FGG.DeBruijn.Base
import Lens.Micro (Lens, (&), (<<%~), (%~), (.~))
import Lens.Micro.TH (makeLenses)


data UCS a ts ti f m x = UCS
  { _parsUnused  :: Set a
  , _strsUnused  :: Set ts
  , _intsUnused  :: Set ti
  , _fldsUnused  :: Set f
  , _methsUnused :: Set m
  , _varsUnused  :: Set x
  }

makeLenses 'UCS




-- |The empty usage checking state.
emptyUCS :: UCS Z Z Z Z Z Z
emptyUCS = UCS S.empty S.empty S.empty S.empty S.empty S.empty



-- |Check whether or not all names are relevant in a program.
checkUsageProg :: Prog -> Bool
checkUsageProg (FDecls fds) = fst (runIxState (checkUsageFDecls fds) emptyUCS)



-- |Check whether or not all names are relevant in a program.
checkUsageFDecls :: (IxMonadState ims, Ord f)
                 => FDecls f
                 -> ims (UCS Z Z Z f Z Z) (UCS Z Z Z f Z Z) Bool
checkUsageFDecls (NewF fds) = do

  -- Check the usage of the remaining declarations.
  grow fldsUnused
  fdsOk <- checkUsageFDecls fds
  _fldUsed <- shrink fldsUnused
  return fdsOk

checkUsageFDecls (MDecls mds) = checkUsageMDecls mds



-- |Check whether or not all names are relevant in a program.
checkUsageMDecls :: (IxMonadState ims, Ord f, Ord m)
                 => MDecls f m
                 -> ims (UCS Z Z Z f m Z) (UCS Z Z Z f m Z) Bool
checkUsageMDecls (NewM mds) = do

  -- Check the usage of the remaining declarations.
  grow methsUnused
  mdsOk <- checkUsageMDecls mds
  methUsed <- shrink methsUnused
  return (methUsed && mdsOk)

checkUsageMDecls (TyDecls tys) = checkUsageTyDecls tys



-- |Check whether or not all names are relevant in a program.
checkUsageTyDecls :: (IxMonadState ims, Ord ts, Ord ti, Ord f, Ord m)
                  => TyDecls ts ti f m
                  -> ims (UCS Z ts ti f m Z) (UCS Z ts ti f m Z) Bool
checkUsageTyDecls (LetStruct (parBnds :: Vec _ a) fldNamesAndTys tys) = do
  let a = vlength parBnds :: Nat a

  -- Collect usage from the parameter bounds.
  imapM_ useType (vlist parBnds)

  hasOrd a $ do

    -- Collect usage from the field types.
    let (_fldNames, fldTys) = unzip (vlist fldNamesAndTys)
    fresh parsUnused a
    imapM_ useType fldTys
    _parsUsed <- clear parsUnused

    -- Continue only if all type parameters were used.
    -- if not parsUsed then return False else do

    -- Check the usage of the remaining declarations.
    grow strsUnused
    tysOk <- checkUsageTyDecls tys
    tsUsed <- shrink strsUnused
    return (tsUsed && tysOk)

checkUsageTyDecls (LetInterface (parBnds :: Vec _ a) parents methNamesAndSigs tys) = do
  let a = vlength parBnds :: Nat a

  -- Collect usage from the parameter bounds.
  imapM_ useType (vlist parBnds)

  hasOrd a $ do

    -- Collect usage from the parent interfaces and method signatures.
    let (_methNames, methSigs) = unzip (vlist methNamesAndSigs)
    fresh parsUnused a
    imapM_ useType (vlist parents)
    grow intsUnused
    methParsUsed <- imapM (checkUsageMSig a) methSigs
    objParsUsed <- clear parsUnused
    let _parsUsed = and (objParsUsed : methParsUsed)

    -- Continue only if all type parameters were used.
    -- if not parsUsed then shrink intsUnused >> return False else do

    -- Check the usage of the remaining declarations.
    tysOk <- checkUsageTyDecls tys
    tiUsed <- shrink intsUnused
    return (tiUsed && tysOk)

checkUsageTyDecls (TmDecls tms) = checkUsageTmDecls tms



-- |Check whether or not all names are relevant in a program.
checkUsageTmDecls :: (IxMonadState ims, Ord ts, Ord ti, Ord f, Ord m)
                  => TmDecls ts ti f m
                  -> ims (UCS Z ts ti f m Z) (UCS Z ts ti f m Z) Bool
checkUsageTmDecls (LetMethod objParBnds _objTy _m methParBnds argTys retTy body tms) = do
  let a  = vlength objParBnds
  let a' = vlength methParBnds
  let x  = vlength argTys

  hasOrd a $ hasOrd (a' `plus` a) $ hasOrd x $ do

    -- Collect usage from method parameter bounds.
    fresh parsUnused a
    imapM_ useType (vlist methParBnds)

    -- Collect usage from argument types, return type, and body.
    growN parsUnused a a'
    fresh varsUnused (S x)

    imapM_ useType (vlist argTys)
    useType retTy
    useExpr body

    varsUsed <- clear varsUnused
    _parsUsed <- clear parsUnused

    -- Only continue if the method checks out.
    if not varsUsed then return False else

      -- Collect usage from the remaining declarations.
      checkUsageTmDecls tms


checkUsageTmDecls (Main mainTy mainTm) = do

  -- Collect the usage for the main type and expression.
  useType mainTy
  useExpr mainTm
  return True



-- |Collect the name usage from a method signature.
checkUsageMSig :: (IxMonadState ims, Ord a, Ord ts, Ord ti)
                 => Nat a
                 -> MSig a ts ti
                 -> ims (UCS a ts ti f m x) (UCS a ts ti f m x) Bool
checkUsageMSig a (MSig methParBnds objTy argTys retTy) = do
  let a' = vlength methParBnds

  -- Collect the usage in the method type parameter bounds.
  imapM_ useType (vlist methParBnds)

  -- Collect the usage in the object, argument, and return types.
  hasOrd (a' `plus` a) $ do

    growN parsUnused a a'
    useTyCon objTy
    imapM_ useType (vlist argTys)
    useType retTy
    shrinkN parsUnused a a'



-- |Collect the name usage from an expression.
useExpr :: (IxMonadState ims, Ord a, Ord ts, Ord ti, Ord f, Ord m, Ord x)
                  => Expr a ts ti f m x
                  -> ims (UCS a ts ti f m x) (UCS a ts ti f m x) ()
useExpr (Var x) =
  use varsUnused x

useExpr (Struct ts tyArgs flds) = do
  use strsUnused ts
  imapM_ useType (vlist tyArgs)
  imapM_ useExpr (fst <$> vlist flds)

useExpr (Select obj _objTy _f) =
  useExpr obj

useExpr (Call obj _objTy m tyArgs args) = do
  useExpr obj
  use methsUnused m
  imapM_ useType (vlist tyArgs)
  imapM_ useExpr (fst <$> vlist args)

useExpr (Assert obj _objTy assTy) = do
  useExpr obj
  useType assTy



-- |Collect the name usage from a type.
useType :: (IxMonadState ims, Ord a, Ord ts, Ord ti)
               => Type a ts ti
               -> ims (UCS a ts ti f m x) (UCS a ts ti f m x) ()
useType (Par a) = use parsUnused a
useType (Con tc tyArgs) = do useTyCon tc; imapM_ useType (vlist tyArgs)



-- |Collect the name usage from a type constructor.
useTyCon :: (IxMonadState ims, Ord a, Ord ts, Ord ti)
               => TyCon ts ti
               -> ims (UCS a ts ti f m x) (UCS a ts ti f m x) ()
useTyCon (TyS _ts) = return ()
useTyCon (TyI ti) = use intsUnused ti


-- * Usage checking combinators



-- |Use a variable name.
use :: (IxMonadState ims, Ord n)
    => Lens (UCS a ts ti f m x) (UCS a ts ti f m x) (Set n) (Set n)
    -> n
    -> ims (UCS a ts ti f m x) (UCS a ts ti f m x) ()
use fld n = do
  ucs <- iget
  let ucs' = ucs & fld %~ S.delete n
  iput ucs'



-- |Grow the usage set for a specific kind by one.
grow :: (IxMonadState ims, Ord n)
     => Lens (UCS a ts ti f m x) (UCS a' ts' ti' f' m' x') (Set n) (Set (S n))
     -> ims (UCS a ts ti f m x) (UCS a' ts' ti' f' m' x') ()
grow fld = do
  ucs <- iget
  let ucs' = ucs & fld %~ grow'
  iput ucs'
  where
    grow' = S.insert FZ . S.mapMonotonic FS



-- |Shrink the usage set for a specific kind by one. Returns whether or not the removed variable was used.
shrink :: (IxMonadState ims, Ord n)
       => Lens (UCS a ts ti f m x) (UCS a' ts' ti' f' m' x') (Set (S n)) (Set n)
       -> ims (UCS a ts ti f m x) (UCS a' ts' ti' f' m' x') Bool
shrink fld = do
  ucs <- iget
  let (unused, ucs') = ucs & fld <<%~ shrink'
  iput ucs'
  return (S.notMember FZ unused)
  where
    shrink' = S.mapMonotonic fromFS . S.delete FZ



-- |Grow the usage set for a specific kind by N.
growN :: (IxMonadState ims, Ord n, Ord (n' :+ n))
      => Lens (UCS a ts ti f m x) (UCS a' ts' ti' f' m' x') (Set n) (Set (n' :+ n))
      -> Nat n
      -> Nat n'
      -> ims (UCS a ts ti f m x) (UCS a' ts' ti' f' m' x') ()
growN fld (n :: Nat n) (n' :: Nat n') = do
  ucs <- iget
  let ucs' = ucs & fld %~ growN'
  iput ucs'
  where
    new :: Set (n' :+ n)
    new = S.fromAscList (map (inject n) (vlist (allFin n')))

    growN' :: Set n -> Set (n' :+ n)
    growN' old = new `S.union` S.mapMonotonic (raise n') old



-- |Shrink the usage set for a specific kind by N. Returns whether or not the removed variables were used.
shrinkN :: (IxMonadState ims, Ord n, Ord (n' :+ n))
      => Lens (UCS a ts ti f m x) (UCS a' ts' ti' f' m' x') (Set (n' :+ n)) (Set n)
      -> Nat n
      -> Nat n'
      -> ims (UCS a ts ti f m x) (UCS a' ts' ti' f' m' x') Bool
shrinkN fld (n :: Nat n) (n' :: Nat n') = do
  ucs <- iget
  let (unused, ucs') = ucs & fld <<%~ shrinkN'
  iput ucs'
  return (unused `S.disjoint` new)
  where
    new :: Set (n' :+ n)
    new = S.fromAscList (map (inject n) (vlist (allFin n')))

    shrinkN' :: Set (n' :+ n) -> Set n
    shrinkN' old = S.mapMonotonic (lower n') (old \\ new)


-- |Sets the usage set for a specific kind.
fresh :: (IxMonadState ims, Ord n)
    => Lens (UCS a ts ti f m x) (UCS a' ts' ti' f' m' x') (Set Z) (Set n)
    -> Nat n
    -> ims (UCS a ts ti f m x) (UCS a' ts' ti' f' m' x') ()
fresh fld n = do
  ucs <- iget
  let ucs' = ucs & fld .~ S.fromAscList (vlist (allFin n))
  iput ucs'



-- |Unsets the usage set for a specific kind. Returns whether or not all names were used.
clear :: (IxMonadState ims)
      => Lens (UCS a ts ti f m x) (UCS a' ts' ti' f' m' x') (Set n) (Set Z)
      -> ims (UCS a ts ti f m x) (UCS a' ts' ti' f' m' x') Bool
clear fld = do
  ucs <- iget
  let (usage, ucs') = ucs & fld <<%~ const S.empty
  iput ucs'
  return (S.null usage)



-- * Rebindable Syntax

(>>=) :: IxMonad m => m i j a -> (a -> m j k b) -> m i k b
(>>=)  = flip ibind

(>>) :: IxMonad m => m i j a -> m j k b -> m i k b
(>>)  = (. const) . (>>=)

return :: IxPointed m => a -> m i i a
return = ireturn

fail :: String -> a
fail = error

ifThenElse :: Bool -> a -> a -> a
ifThenElse cond yes no = bool yes no cond

imapM :: (IxMonadState ims) => (a -> ims i i b) -> [a] -> ims i i [b]
imapM _ [] = return []
imapM f (x : xs) = do y <- f x; ys <- imapM f xs; return (y : ys)

imapM_ :: (IxMonadState ims) => (a -> ims i i b) -> [a] -> ims i i ()
imapM_ f xs = imapM f xs >> return ()

-- -}
-- -}
-- -}
-- -}
-- -}
