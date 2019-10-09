{-# OPTIONS -fno-warn-partial-type-signatures #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE EmptyDataDeriving     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}



module Language.FGG.DeBruijn.Typing where



import Data.Bifunctor
import Data.Coolean
import Data.Either (either)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Maybe (isJust, fromJust)
import Data.List (sort)
import Data.Set (Set)
import qualified Data.Set as S
import Debug.Trace (trace)
import Language.FGG.Common
import Language.FGG.DeBruijn.Base
import Text.Printf
import Unsafe.Coerce (unsafeCoerce)


-- The following rule suppresses warnings,
-- comment it out to show warnings while type-checking:
-- {-# RULES "warn/quiet" forall msg cond. warn msg cond = cond #-}

{-# NOINLINE warn #-}
warn :: (Coolean cool) => String -> cool -> cool
warn msg cond
  | not (toBool cond) = trace msg cond
  | otherwise         = cond

-- ** Type checking programs

data TCS ts ti f m = (Fin ts, Fin ti, Fin f, Fin m) => TCS
  { methSigsI :: Map (ti, m) (TySig MSig ts ti)
  , methSigsS :: Map (ts, m) (TySig MSig ts ti)
  , methSetI  :: ti -> Set m
  , methSetS  :: ts -> Set m
  , fldSig    :: Map (ts, f) (TySig FSig ts ti)
  , strSig    :: ts -> TySig SSig ts ti
  , intSig    :: ti -> TySig ISig ts ti
  , methUndef :: Set m
  , fldUndef  :: Set f
  }


-- |Retrieve the method set for any type constructor.
methSet :: forall ts ti f m. TCS ts ti f m -> TyCon ts ti -> Set m
methSet TCS{..} (TyS ts) = methSetS ts
methSet TCS{..} (TyI ti) = methSetI ti


-- |Retrieve the method signature for any type constructor.
methSig :: forall ts ti f m. TCS ts ti f m -> (TyCon ts ti, m) -> Maybe (TySig MSig ts ti)
methSig TCS{..} (TyS ts, m) = M.lookup (ts, m) methSigsS
methSig TCS{..} (TyI ti, m) = M.lookup (ti, m) methSigsI


-- |Retrieve the type parameter bounds for any type constructor.
tyParBnds :: forall ts ti f m.
             TCS ts ti f m
          -> TyCon ts ti
          -> forall b. (forall a. Vec (Type Z ts ti) a -> b) -> b
tyParBnds TCS{..} (TyS ts) k = case strSig ts of TySig parBnds _ -> k parBnds
tyParBnds TCS{..} (TyI ti) k = case intSig ti of TySig parBnds _ -> k parBnds


-- |Type check programs.
checkProg :: Prog -> Cool
checkProg (FDecls fds) = checkFDecls Z fds


-- |Type check field name declarations.
checkFDecls :: (Fin f) => Nat f -> FDecls f -> Cool
checkFDecls fldNum (NewF fds) = checkFDecls (S fldNum) fds
checkFDecls fldNum (MDecls mds) = checkMDecls fldNum Z mds


-- |Type check method name declarations.
checkMDecls :: (Fin f, Fin m) => Nat f -> Nat m -> MDecls f m -> Cool
checkMDecls fldNum methNum (NewM mds) = checkMDecls fldNum (S methNum) mds
checkMDecls fldNum methNum (TyDecls tys) = checkTyDecls tcs tys
  where
    tcs = TCS
      { methSigsI = M.empty
      , methSigsS = M.empty
      , methSetI  = fromZ
      , methSetS  = fromZ
      , fldSig    = M.empty
      , strSig    = fromZ
      , intSig    = fromZ
      , methUndef = S.fromAscList (vlist (allFin methNum))
      , fldUndef  = S.fromAscList (vlist (allFin fldNum))
      }


-- |Type check type declarations.
checkTyDecls :: forall ts ti f m. TCS ts ti f m -> TyDecls ts ti f m -> Cool
checkTyDecls tcs@TCS{..} (LetStruct (parBnds :: Vec _ a) fldsAndTys rest)
  = fldsUniq &&& fldTysOk &&& parBndsOk &&& checkTyDecls tcs' rest
  where
    fldsUniq :: Bool
    fldsUniq = warn "checkTyDecls.fldsUniq"
             $ allDifferent (vlist (vmap fst fldsAndTys))

    parBndsOk :: Bool
    parBndsOk = warn "checkTyDecls.parBndsOk"
              $ vall isTyI parBnds && vall (checkType tcs Nil Nil) parBnds

    parBnds' :: Vec (Type Z (S ts) ti) a
    parBnds' = vmap (bimap FS id) parBnds

    methSigsI' :: Map (ti, m) (TySig MSig (S ts) ti)
    methSigsI' = M.map (bimap FS id) methSigsI

    methSigsS' :: Map (S ts, m) (TySig MSig (S ts) ti)
    methSigsS' = M.mapKeysMonotonic (bimap FS id) (M.map (bimap FS id) methSigsS)

    methSetS' :: S ts -> Set m
    methSetS' FZ      = S.empty
    methSetS' (FS ts) = methSetS ts

    fldSig' :: Map (S ts, f) (TySig FSig (S ts) ti)
    fldSig' = M.unions [newFldSig, oldFldSig]
      where
        newFldSig = M.fromList (vlist (vmap mkFldSig fldsAndTys))
          where
            mkFldSig :: (f, Type a ts ti) -> ((S ts, f), TySig FSig (S ts) ti)
            mkFldSig (f, fldTy) = ((FZ, f), TySig parBnds' (FSig (bimap FS id fldTy)))
        oldFldSig = M.mapKeysMonotonic (bimap FS id) (M.map (bimap FS id) fldSig)

    strSig' :: S ts -> TySig SSig (S ts) ti
    strSig' FZ      = TySig (vmap (bimap FS id) parBnds) (SSig (vmap (bimap FS id . snd) fldsAndTys))
    strSig' (FS ts) = bimap FS id (strSig ts)

    intSig' :: ti -> TySig ISig (S ts) ti
    intSig' ti = bimap FS id (intSig ti)

    fldUndef' :: Set f
    fldUndef' = S.difference fldUndef (S.fromList (vlist (vmap fst fldsAndTys)))

    tcs' :: TCS (S ts) ti f m
    tcs' = TCS methSigsI' methSigsS' methSetI methSetS' fldSig' strSig' intSig' methUndef fldUndef'

    fldTysOk :: Bool
    fldTysOk = warn "checkTyDecls.fldTysOk"
             $ vall (checkType tcs parBnds Nil) (vmap snd fldsAndTys)

checkTyDecls tcs@TCS{..} (LetInterface (parBnds :: Vec _ a) parents methNamesAndSigs rest)
  = methsUniq &&& parBndsOk &&& isJust parentMethSigsI !&& methSigsOk &&& checkTyDecls tcs' rest
  where
    methsUniq :: Bool
    methsUniq = warn "checkTyDecls.methsUniq"
              $ allDifferent (vlist (vmap fst methNamesAndSigs))

    parBndsOk :: Bool
    parBndsOk = warn "checkTyDecls.parBndsOk"
              $ vall isTyI parBnds && vall (checkType tcs Nil Nil) parBnds

    parBnds' :: Vec (Type Z ts (S ti)) a
    parBnds' = vmap (bimap id FS) parBnds

    methSigsI' :: Map (S ti, m) (TySig MSig ts (S ti))
    methSigsI' = M.unions [newMethSigsI, oldMethSigsI, fromJust parentMethSigsI]
      where
        newMethSigsI = M.fromList (vlist (vmap mkMethSig methNamesAndSigs))
          where
            mkMethSig (m, methSig') = ((FZ, m), TySig parBnds' methSig')
        oldMethSigsI = M.mapKeysMonotonic (bimap FS id) (M.map (bimap id FS) methSigsI)

    parentMethSigsI :: Maybe (Map (S ti, m) (TySig MSig ts (S ti)))
    parentMethSigsI = mkParentMethSigI tcs parBnds parents

    methSigsS' :: Map (ts, m) (TySig MSig ts (S ti))
    methSigsS' = M.map (bimap id FS) methSigsS

    methSetI' :: S ti -> Set m
    methSetI' FZ      = S.fromList (vlist (vmap fst methNamesAndSigs))
    methSetI' (FS ti) = methSetI ti

    fldSig' :: Map (ts, f) (TySig FSig ts (S ti))
    fldSig' = M.map (bimap id FS) fldSig

    strSig' :: ts -> TySig SSig ts (S ti)
    strSig' ts = bimap id FS (strSig ts)

    intSig' :: S ti -> TySig ISig ts (S ti)
    intSig' FZ      = TySig (vmap (bimap id FS) parBnds) ISig
    intSig' (FS ti) = bimap id FS (intSig ti)

    methUndef' :: Set m
    methUndef' = S.difference methUndef (S.fromList (vlist (vmap fst methNamesAndSigs)))

    tcs' :: TCS ts (S ti) f m
    tcs' = TCS methSigsI' methSigsS' methSetI' methSetS fldSig' strSig' intSig' methUndef' fldUndef

    methSigsOk :: Bool
    methSigsOk = warn "checkTyDecls.methSigsOk"
               $ vall (checkMSig tcs' parBnds') (vmap snd methNamesAndSigs)

checkTyDecls tcs@TCS{..} (TmDecls rest)
  | S.null fldUndef = checkTmDecls tcs rest
  | otherwise       = false


-- |Type check method signatures.
checkMSig :: forall a ts ti f m.
             (Fin a)
          => TCS ts ti f m
          -> Vec (Type Z ts ti) a
          -> MSig a ts ti
          -> Bool
checkMSig tcs@TCS{..} objParBnds (MSig (methParBnds :: Vec _ a') _objTy argTys retTy) =
  methParBndsOk && argAndRetTysOk
  where
    methParBndsOk :: Bool
    methParBndsOk = warn "checkMSig.methParBndsOk"
                  $ vall isTyI methParBnds && vall (checkType tcs objParBnds Nil) methParBnds

    argAndRetTysOk :: Bool
    argAndRetTysOk = warn "checkMSig.argAndRetTysOk"
                   $ plusEq @a' @a (vlength methParBnds)
                   $ vall (checkType tcs objParBnds methParBnds) (Cons retTy argTys)

-- |Type check method declarations.
checkTmDecls :: forall ts ti f m. TCS ts ti f m -> TmDecls ts ti f m -> Cool
checkTmDecls tcs@TCS{..}
  (LetMethod (objParBnds :: Vec _ a) objTy m (methParBnds :: Vec _ a') (argTys :: Vec _ n) retTy body rest)
  = methUniq &&& objParBndsOk &&& methParBndsOk &&& bodyOk &&& restOk
  where
    methUniq :: Bool
    methUniq = warn "checkTmDecls.methUniq"
             $ M.notMember (objTy, m) methSigsS

    objParBndsOk :: Bool
    objParBndsOk = warn "checkTmDecls.objParBndsOk"
                 $ vall isTyI objParBnds && vall (checkType tcs Nil Nil) objParBnds

    methParBndsOk :: Bool
    methParBndsOk = warn "checkTmDecls.methParBndsOk"
                  $ vall isTyI methParBnds && vall (checkType tcs objParBnds Nil) methParBnds

    newMethSig :: TySig MSig ts ti
    newMethSig = TySig objParBnds (MSig methParBnds (TyS objTy) argTys retTy)

    methSigsS' :: Map (ts, m) (TySig MSig ts ti)
    methSigsS' = M.insert (objTy, m) newMethSig methSigsS

    methSetS' :: ts -> Set m
    methSetS' ts
      | ts == objTy = S.insert m (methSetS ts)
      | otherwise   = methSetS ts

    methUndef' :: Set m
    methUndef' = S.delete m methUndef

    tcs' :: TCS ts ti f m
    tcs' = TCS methSigsI methSigsS' methSetI methSetS' fldSig strSig intSig methUndef' fldUndef

    objTy' :: Type (a' :+ a) ts ti
    objTy' = Con (TyS objTy) (vmap (Par . raise (vlength methParBnds)) (allFin (vlength objParBnds)))

    tyEnv :: S n -> Type (a' :+ a) ts ti
    tyEnv FZ     = objTy'
    tyEnv (FS n) = vlookup argTys n

    bodyOk = checkExpr tcs' objParBnds methParBnds tyEnv retTy body

    restOk = checkTmDecls tcs' rest

checkTmDecls tcs@TCS{..} (Main retTy body)
  | S.null methUndef = checkExpr tcs Nil Nil fromZ retTy body
  | otherwise        = warn "checkTmDecls.methUndef" false



-- |Type check expressions.
checkExpr :: forall a' a ts ti f m x.
             (Fin a', Fin a, Fin (a' :+ a))
          => TCS ts ti f m
          -> Vec (Type Z ts ti) a
          -> Vec (Type a ts ti) a'
          -> (x -> Type (a' :+ a) ts ti)
          -> Type (a' :+ a) ts ti
          -> Expr (a' :+ a) ts ti f m x
          -> Cool
checkExpr tcs@TCS{..} objParBnds methParBnds tyEnv = go
  where
    go :: Type (a' :+ a) ts ti
       -> Expr (a' :+ a) ts ti f m x
       -> Cool

    -- Case: Variables
    go ty (Var x)
      = toCool (ty == tyEnv x)

    -- Case: Struct Literals
    go ty (Struct ts tyArgs (argsAndTys :: Vec _ n2))
      = case strSig ts of
        TySig parBnds (SSig argTys) ->
          case ( vlength parBnds `decEq` vlength tyArgs
               , vlength argTys  `decEq` vlength argsAndTys
               ) of
          (Nothing, _) -> false
          (_, Nothing) -> false
          (Just Refl, Just Refl) ->
            tyOk &&& tyArgsOk &&& argTysOk !&& argsOk
            where
              -- Is the return type correct?
              ty'      = Con (TyS ts) tyArgs
              tyOk     = warn (printf "checkExpr.Struct.tyOk: Expected: %s, Found: %s" (show ty) (show ty'))
                       $ ty == ty'
              -- Is each type parameter within the expected bounds?
              tyArgsOk = warn "checkExpr.Struct.tyArgsOk"
                       $ vall (checkType tcs objParBnds methParBnds) tyArgs
                      && checkParBnds tcs objParBnds methParBnds parBnds tyArgs

              -- Is each argument type within the expected bounds?
              argTysOk = warn "checkExpr.Struct.argTysOk"
                       $ checkParBnds' tcs objParBnds methParBnds argTys' tys
                where
                  tys     = vmap snd argsAndTys
                  argTys' = vmap (substType (vlookup tyArgs)) argTys
              -- Is each argument well-typed?
              argsOk   = warn "checkExpr.Struct.argsOk"
                       $ vall' (\(arg, argTy) -> go argTy arg) argsAndTys

    -- Case: Select
    go ty (Select obj objTy@(Con (TyS ts) tyArgs) f)
      = case M.lookup (ts, f) fldSig of
        Nothing -> false
        Just (TySig parBnds' (FSig fldTy)) ->
          case vlength parBnds' `decEq` vlength tyArgs of
          Nothing -> false
          Just Refl ->
            tyOk &&& tyArgsOk !&& objTyOk
            where
              -- Is the return type correct?
              tyOk = ty == substType (vlookup tyArgs) fldTy
              -- Is each type parameter within the expected bounds?
              tyArgsOk = vall (checkType tcs objParBnds methParBnds) tyArgs
                      && checkParBnds tcs objParBnds methParBnds parBnds' tyArgs
              -- Is the object well-typed?
              objTyOk  = go objTy obj

    -- Case: Method Calls
    go ty (Call obj objTy@(Con tc objTyArgs) m methTyArgs (argsAndTys :: Vec _ n))
      = case methSig tcs (tc, m) of
        Nothing -> false
        Just (TySig (objParBnds' :: Vec _ a1) (MSig (methParBnds' :: Vec _ a2) objTc argTys retTy)) ->
          -- Are the number of type arguments correct?
          case ( vlength objParBnds'  `decEq` vlength objTyArgs
               , vlength methParBnds' `decEq` vlength methTyArgs
               , vlength argsAndTys   `decEq` vlength argTys
               ) of
          (Nothing, _, _) -> false
          (_, Nothing, _) -> false
          (_, _, Nothing) -> false
          (Just Refl, Just Refl, Just Refl) ->
            objTyOk &&& retTyOk !&& objTyArgsOk &&& methTyArgsOk !&& argsOk &&& objOk
            where
              s :: (a2 :+ a1) -> Type (a' :+ a) ts ti
              s = either id id . vlookupEither methTyArgs objTyArgs
              -- Is the object type ok?
              objTyOk = warn "checkExpr.Call.objTyOk"
                      $ tc == objTc
              -- Is the return type correct?
              retTyOk = warn "checkExpr.Call.retTyOk"
                      $ ty == substType s retTy
              -- Is each type argument within the expected bounds?
              objTyArgsOk  = warn "checkExpr.Call.objTyArgsOk"
                           $ checkParBnds tcs objParBnds methParBnds objParBnds' objTyArgs
              methTyArgsOk = warn "checkExpr.Call.methTyArgsOk"
                           $ checkParBnds' tcs objParBnds methParBnds methParBnds'' methTyArgs
                where
                  methParBnds'' :: Vec (Type (a' :+ a) ts ti) a2
                  methParBnds'' = vmap (substType (vlookup objTyArgs)) methParBnds'
              -- Is each argument well-typed?
              argsOk = warn "checkExpr.Call.argsOk"
                     $ vand' (vzip go argTys' args)
                where
                  args :: Vec (Expr (a' :+ a) ts ti f m x) n
                  args = vmap fst argsAndTys
                  argTys' :: Vec (Type (a' :+ a) ts ti) n
                  argTys' = vmap (substType s) argTys
              -- Is the object well-typed?
              objOk = go objTy obj

    -- Case: Type Assertions
    go ty@(Con (TyI _) _) (Assert obj objTy@(Con (TyI _) _) assTy)
      | ty == assTy = go objTy obj

    go ty@(Con (TyS _) _) (Assert obj objTy@(Con (TyI _) _) assTy)
      | ty == assTy = assTyOk !&& go objTy obj
      where
        assTyOk = implements tcs objParBnds methParBnds assTy objTy

    go _ _ = false


-- |Check if type is well-formed.
checkType :: forall a a' ts ti f m.
             (Fin a, Fin (a' :+ a))
          => TCS ts ti f m
          -> Vec (Type Z ts ti) a
          -> Vec (Type a ts ti) a'
          -> Type (a' :+ a) ts ti
          -> Bool
checkType _ _ _ (Par _) = True
checkType tcs@TCS{..} objParBnds methParBnds (Con tc tyArgs) =
  tyParBnds tcs tc $ \parBnds ->
    case vlength tyArgs `decEq` vlength parBnds of
      Nothing   -> False
      Just Refl -> checkParBnds tcs objParBnds methParBnds parBnds tyArgs
                && vall (checkType tcs objParBnds methParBnds) tyArgs


-- |Check if type is an interface.
isTyI :: forall a ts ti. Type a ts ti -> Bool
isTyI (Con (TyI _) _) = True
isTyI _               = False


-- |Check if argument types implement parameter bounds.
checkParBnds :: forall a' a ts ti f m n.
                (Fin (a' :+ a), Fin ts , Fin ti, Ord m)
             => TCS ts ti f m
             -> Vec (Type Z ts ti) a
             -> Vec (Type a ts ti) a'
             -> Vec (Type Z ts ti) n
             -> Vec (Type (a' :+ a) ts ti) n
             -> Bool
checkParBnds tcs objParBnds methParBnds parBnds tys
  = checkParBnds' tcs objParBnds methParBnds (unsafeCoerce parBnds) tys


-- |Check if argument types implement parameter bounds.
checkParBnds' :: forall a' a ts ti f m n.
                (Fin (a' :+ a), Fin ts , Fin ti, Ord m)
             => TCS ts ti f m
             -> Vec (Type Z ts ti) a
             -> Vec (Type a ts ti) a'
             -> Vec (Type (a' :+ a) ts ti) n
             -> Vec (Type (a' :+ a) ts ti) n
             -> Bool
checkParBnds' tcs objParBnds methParBnds parBnds tys
  = vand (vzip (implements tcs objParBnds methParBnds) parBnds tys)


-- |Check whether one type implements another.
implements :: forall a' a ts ti f m.
              (Fin (a' :+ a), Fin ts , Fin ti, Ord m)
           => TCS ts ti f m
           -> Vec (Type Z ts ti) a
           -> Vec (Type a ts ti) a'
           -> Type (a' :+ a) ts ti
           -> Type (a' :+ a) ts ti
           -> Bool
implements tcs@TCS{..} objParBnds methParBnds = go
  where
    go :: Type (a' :+ a) ts ti
       -> Type (a' :+ a) ts ti
       -> Bool

    -- implements <:-param and <:-struct
    go ty1 ty2 | ty1 == ty2 = True

    -- implements <:-bounds
    go (Par a) ty
      = case vlookupEither methParBnds objParBnds a of
        Left methParBnd ->
          let methParBnd' = mapPar (raise (vlength methParBnds)) methParBnd
          in go methParBnd' ty
        Right objParBnd ->
          let objParBnd' = unsafeCoerce objParBnd
          in go objParBnd' ty
          -- NOTE: unsafeCoerce above is equivalent to the following expression:
          -- mapPar (inject (vlength methParBnds `plus` vlength objParBnds))

    -- implements <:-interface (TODO: check w/ Phil)
    go (Con tc1 tyArgs1) (Con (TyI ti2) tyArgs2)
      = case vlength tyArgs1 `decEq` vlength tyArgs2 of
        Nothing   -> False
        Just Refl -> subsetOk && tyArgsOk
          where
            methSet1 = methSet tcs tc1
            methSet2 = methSetI ti2
            subsetOk = methSet2 `S.isSubsetOf` methSet1
            tyArgsOk = S.foldr (\m b -> tyArgOk m && b) True methSet2
              where
                tyArgOk :: m -> Bool
                tyArgOk m =
                  case (methSig tcs (tc1, m), M.lookup (ti2, m) methSigsI) of
                  (Nothing, _) -> False
                  (_, Nothing) -> False
                  (Just (TySig parBnds1 msig1), Just (TySig parBnds2 msig2)) ->
                    case ( vlength parBnds1 `decEq` vlength parBnds2
                         , vlength parBnds1 `decEq` vlength tyArgs1
                         ) of
                    (Nothing, _) -> False
                    (_, Nothing) -> False
                    (Just Refl, Just Refl) ->
                      case ( substMethSig (vlookup tyArgs1) msig1
                           , substMethSig (vlookup tyArgs2) msig2
                           ) of
                      (   MSig (tyArgs1' :: Vec _ a'') objTy1 argTys1 retTy1
                        , MSig tyArgs2' objTy2 argTys2 retTy2) ->
                        case ( vlength tyArgs1' `decEq` vlength tyArgs2'
                             , vlength argTys1  `decEq` vlength argTys2
                             ) of
                        (Nothing, _) -> False
                        (_, Nothing) -> False
                        (Just Refl, Just Refl) ->
                          tyArgsOk' && objTysOk && argTysOk && retTysOk
                          where
                          tyArgsOk' = tyArgs1' == tyArgs2'
                          objTysOk  = objTy1 == objTy2
                          argTysOk  = plusEq @a'' @(a' :+ a) (vlength tyArgs1') (argTys1 == argTys2)
                          retTysOk  = plusEq @a'' @(a' :+ a) (vlength tyArgs1') (retTy1  == retTy2)

    -- catch all: false
    go _ _ = False



-- |Extend the method signature mapping with the methods  in a new interface,
-- inherited from parent interfaces.
mkParentMethSigI :: forall a ts ti f m p.
                    (Fin a)
                 => TCS ts ti f m
                 -> Vec (Type Z ts ti) a
                 -> Vec (Type a ts ti) p
                 -> Maybe (Map (S ti, m) (TySig MSig ts (S ti)))
mkParentMethSigI tcs@TCS{..} parBnds = go1
  where
    -- Construct all parent method signatures, or fail.
    go1 :: forall p'. Vec (Type a ts ti) p' -> Maybe (Map (S ti, m) (TySig MSig ts (S ti)))
    go1 Nil = Just M.empty
    go1 (Cons (Par _) _) = Nothing
    go1 (Cons (Con (TyS _) _) _) = Nothing
    go1 (Cons (Con (TyI ti) tyArgs) parents) =
      mconcat
        [ go2 m methSig' tyArgs
        | m <- S.toList (methSetI ti)
        , let Just methSig' = M.lookup (ti, m) methSigsI
        ]
        <>
      go1 parents

    -- Construct a single parent method signature out of the required parts,
    -- making sure each type argument implements its corresponding bound.
    go2 :: forall a'.
           m
        -> TySig MSig ts ti
        -> Vec (Type a ts ti) a'
        -> Maybe (Map (S ti, m) (TySig MSig ts (S ti)))
    go2 m (TySig parBnds' methSig') tyArgs' =
      case vlength parBnds' `decEq` vlength tyArgs' of
        Nothing   -> Nothing
        Just Refl -> M.singleton (FZ, m) methSig''
                     `onlyIf`
                     checkParBnds tcs parBnds Nil parBnds' tyArgs'
          where
            methSig'' :: TySig MSig ts (S ti)
            methSig'' = bimap id FS (TySig parBnds (substMethSig (vlookup tyArgs') methSig'))

            onlyIf :: forall a''. a'' -> Bool -> Maybe a''
            onlyIf x True  = Just x
            onlyIf _ False = Nothing


-- * Helper functions

allDifferent :: Ord a => [a] -> Bool
allDifferent = pairwiseDifferent . sort

pairwiseDifferent :: Eq a => [a] -> Bool
pairwiseDifferent xs = and $ zipWith (/=) xs (drop 1 xs)

-- -}
-- -}
-- -}
-- -}
-- -}
