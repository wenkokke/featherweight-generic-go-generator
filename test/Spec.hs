{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings #-}

import Control.Monad (void)
import qualified Data.Coolean as NEAT
import Data.Text (Text)
import qualified Data.Text as T
import Language.FGG.Common
  ( TyCon(..)
  , S(..)
  , Vec(..))
import Language.FGG.DeBruijn
  ( Prog(..)
  , FDecls(..)
  , MDecls(..)
  , TyDecls(..)
  , TmDecls(..)
  , Expr(..)
  , Type(..)
  , MSig(..))
import qualified Language.FGG.Named as N
import qualified Language.FGG.DeBruijn as DB
import Test.HUnit

main :: IO ()
main = void (runTestTT tests)

tests :: Test
tests = TestList
  [ checkProg bool          ~? "Rejected well-typed program 'bools'"
  , ex1Src ~=? showProg ex1
  , not (checkProg ex2a)    ~? "Accepted ill-typed program 'ex2a'"
  ,      checkProg ex2b     ~? "Rejected well-typed program 'ex2b'"
  , not (checkProg ex3)     ~? "Accepted ill-typed program 'ex3'"
  , not (checkProg ex4)     ~? "Accepted ill-typed program 'ex4'"
  ]

instance Show (Prog ann) where
  show = T.unpack . showProg

checkProg :: Show ann => Prog ann -> Bool
checkProg = NEAT.toBool . DB.checkProg

showProg :: Prog ann -> Text
showProg = N.prettyProg . DB.convProg


-- Bool example from the paper
bool :: Prog Int
bool
  = FDecls 1
  $ MDecls 2
  $ NewM {-PAY-} 3
  $ TyDecls 4

    -- type TT struct {};
  $ LetStruct {-PAY-} 5 Nil Nil

    -- type FF struct {};
  $ LetStruct {-PAY-} 6 Nil Nil

    -- type Bool interface { Not() Bool };
  $ LetInterface {-PAY-} 7
    Nil
    Nil
    (Cons (FZ, MSig Nil (TyI FZ) Nil (Con {-PAY-} (TyI FZ) Nil)) Nil)
  $ TmDecls 8

    -- func (this TT) Not() { return FF };
  $ LetMethod {-PAY-} 9
    Nil                                 -- Object type parameter bounds
    FZ                                  -- Object type name
    FZ                                  -- Method name
    Nil                                 -- Method type parameter bounds
    Nil                                 -- Method argument types
    (Con {-PAY-} (TyS (FS FZ)) Nil)     -- Method return type
    (Struct {-PAY-} 10 (FS FZ) Nil Nil) -- Method body

    -- func (this FF) Not() { return TT };
  $ LetMethod {-PAY-} 11
    Nil                                 -- Object type parameter bounds
    (FS FZ)                             -- Object type name
    FZ                                  -- Method name
    Nil                                 -- Method type parameter bounds
    Nil                                 -- Method argument types
    (Con {-PAY-} (TyS FZ) Nil)          -- Method return type
    (Struct {-PAY-} 12 FZ Nil Nil)      -- Method body

    -- func main() { _ = TT.Not() };
  $ Main 13
    (Con {-PAY-} (TyS FZ) Nil)
    (Call {-PAY-} 14
      (Struct {-PAY-} 15 (FS FZ) Nil Nil)
      (Con {-PAY-} (TyS (FS FZ)) Nil)
      FZ
      Nil
      Nil)


-- Bug #1 in printing of type parameters
ex1 :: Prog Int
ex1
  = FDecls 1
  $ NewF {-PAY-} 2
  $ MDecls 3
  $ NewM {-PAY-} 4
  $ TyDecls 5

    -- type ts0(type ) struct {};
  $ LetStruct {-PAY-} 6 Nil Nil

    -- type ts1(type ) struct {};
  $ LetStruct {-PAY-} 7 Nil Nil

    -- type ti0(type ) interface {};
  $ LetInterface {-PAY-} 8 Nil Nil Nil

    -- type ts2(type ) struct { f0 ts1() };
  $ LetStruct {-PAY-} 9
    Nil
    (Cons (FZ, Con {-PAY-} (TyS FZ) Nil) Nil)

  $ TmDecls 10

    -- func (this ts2(type )) m0(type a1 ti0())(x0 a0) ts2() { return this };
  $ LetMethod {-PAY-} 11
    Nil                                   -- Object type parameter bounds
    FZ                                    -- Object type name
    FZ                                    -- Method name
    (Cons (Con {-PAY-} (TyI FZ) Nil) Nil) -- Method type parameter bounds
    (Cons (Par {-PAY-} FZ) Nil)           -- Method argument types
    (Con {-PAY-} (TyS FZ) Nil)            -- Method return type
    (Var {-PAY-} 13 (FS FZ))              -- Method body

    -- func main() { _ = ts1(){} }
  $ Main 14
    (Con {-PAY-} (TyS (FS FZ)) Nil)
    (Struct {-PAY-} 15 (FS FZ) Nil Nil)


ex1Src :: Text
ex1Src = T.intercalate "\n"
  [ "package main;"
  , "type ts0(type ) struct {"
  , ""
  , "};"
  , "type ts1(type ) struct {"
  , ""
  , "};"
  , "type ti0(type ) interface {"
  , ""
  , "};"
  , "type ts2(type ) struct {"
  , "  f0 ts1()"
  , "};"
  , "func (this ts2(type )) m0(type a0 ti0())(x0 a0) ts2() {"
  , "  return x0"
  , "};"
  , "func main() {"
  , "  _ = ts1(){}"
  , "}"
  ]


-- Bug #2 in implements relation?
ex2a :: Prog Int
ex2a
  = FDecls 1
  $ MDecls 2
  $ NewM {-PAY-} 3
  $ TyDecls 4

  $ LetStruct {-PAY-} 5
    Nil
    Nil

  $ LetInterface {-PAY-} 6
    Nil
    Nil
    Nil

  $ LetInterface {-PAY-} 7
    Nil
    Nil
    (Cons (FZ, MSig Nil (TyI FZ) Nil (Con {-PAY-} (TyS FZ) Nil)) Nil)

  $ LetStruct {-PAY-} 8
    (Cons (Con {-PAY-} (TyI FZ) Nil) Nil)
    Nil

  $ TmDecls 9

  $ LetMethod {-PAY-} 10
    (Cons (Con {-PAY-} (TyI (FS FZ)) Nil) Nil)
    FZ
    FZ
    Nil
    Nil
    (Con {-PAY-} (TyS (FS FZ)) Nil)
    (Struct {-PAY-} 11 (FS FZ) Nil Nil)

  $ Main 12
    (Con {-PAY-} (TyS (FS FZ)) Nil)
    (Struct {-PAY-} 13 (FS FZ) Nil Nil)

ex2b :: Prog Int
ex2b
  = FDecls 1
  $ MDecls 2
  $ NewM {-PAY-} 3
  $ TyDecls 4

  $ LetStruct {-PAY-} 5
    Nil
    Nil

  $ LetInterface {-PAY-} 6
    Nil
    Nil
    Nil

  $ LetInterface {-PAY-} 7
    Nil
    Nil
    (Cons (FZ, MSig Nil (TyI FZ) Nil (Con {-PAY-} (TyS FZ) Nil)) Nil)

  $ LetStruct {-PAY-} 8
    (Cons (Con {-PAY-} (TyI (FS FZ)) Nil) Nil)
    Nil

  $ TmDecls 9

  $ LetMethod {-PAY-} 10
    (Cons (Con {-PAY-} (TyI FZ) Nil) Nil)
    FZ
    FZ
    Nil
    Nil
    (Con {-PAY-} (TyS (FS FZ)) Nil)
    (Struct {-PAY-} 11 (FS FZ) Nil Nil)

  $ Main 12
    (Con {-PAY-} (TyS (FS FZ)) Nil)
    (Struct {-PAY-} 13 (FS FZ) Nil Nil)

-- Bug #3
ex3 :: Prog Int
ex3
  = FDecls 1
  $ NewF {-PAY-} 2
  $ MDecls 3
  $ NewM {-PAY-} 4
  $ TyDecls 5

    -- type ts0(type ) struct {};
  $ LetStruct {-PAY-} 6 Nil Nil

    -- type ti0(type ) interface {};
  $ LetInterface {-PAY-} 7 Nil Nil Nil

    -- type ts2(type ) struct {f0 ts0()};
  $ LetStruct {-PAY-} 8
    Nil
    (Cons (FZ, Con {-PAY-} (TyS FZ) Nil) Nil)

  $ TmDecls {-PAY-} 9

    -- func (this ts2(type )) m0(type )(x0 ti0()) ts2() {return ts2(){x0}};
  $ LetMethod {-PAY-} 10
    Nil
    FZ
    FZ
    Nil
    (Cons (Con {-PAY-} (TyI FZ) Nil) Nil)
    (Con {-PAY-} (TyS FZ) Nil)
    (Struct {-PAY-} 10 FZ Nil (Cons (Var {-PAY-} 11 (FS FZ), Con {-PAY-} (TyI FZ) Nil) Nil))

    -- func main() {_ = ts0(){}}
  $ Main {-PAY-} 12
    (Con {-PAY-} (TyS (FS FZ)) Nil)
    (Struct {-PAY-} 13 (FS FZ) Nil Nil)

-- Bug #4
ex4 :: Prog Int
ex4
  = FDecls {-PAY-} 1
  $ MDecls {-PAY-} 2
  $ TyDecls {-PAY-} 3

    -- type ts0(type ) struct {};
  $ LetStruct {-PAY-} 4 Nil Nil
    -- type ts1(type ) struct {};
  $ LetStruct {-PAY-} 5 Nil Nil

  $ TmDecls {-PAY-} 6

    -- func main() {_ = ts0(){}.(ts1()) }
  $ Main {-PAY-} 7
    (Con {-PAY-} (TyS FZ) Nil)
    (Assert {-PAY-}  8
      (Struct {-PAY-} 9 (FS FZ) Nil Nil)
      (Con {-PAY-} (TyS (FS FZ)) Nil)    -- Expression type
      (Con {-PAY-} (TyS FZ) Nil))        -- Asserted type
