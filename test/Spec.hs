{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}

import qualified Data.Coolean as NEAT
import Data.Text (Text)
import qualified Data.Text.IO as T
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
import System.Exit (exitSuccess,exitFailure)

main :: IO ()
main = T.putStrLn $ showProg bug2

exitWith :: Bool -> IO ()
exitWith True  = exitSuccess
exitWith False = exitFailure

checkProg :: Show ann => Prog ann -> Bool
checkProg = NEAT.toBool . DB.checkProg

showProg :: Show ann => Prog ann -> Text
showProg = N.prettyProg . DB.convProg

-- Bools example from the paper
bools :: Prog Int
bools
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
bug1 :: Prog Int
bug1
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


-- Bug #2 in implements relation?
bug2 :: Prog Int
bug2
  = FDecls 1
  $ NewF {-PAY-} 2
  $ MDecls 3
  $ NewM {-PAY-} 4
  $ TyDecls 5

  $ LetStruct {-PAY-} 6
    Nil
    Nil

  $ LetInterface {-PAY-} 7
    Nil
    Nil
    Nil

  $ LetInterface {-PAY-} 8
    Nil
    Nil
    (Cons (FZ, MSig Nil (TyI FZ) Nil (Con {-PAY-} (TyS FZ) Nil)) Nil)

  $ LetStruct {-PAY-} 9
    (Cons (Con {-PAY-} (TyI FZ) Nil) Nil)
    (Cons (FZ, Con {-PAY-} (TyS FZ) Nil) Nil)

  $ TmDecls 10

  $ LetMethod {-PAY-} 11
    (Cons (Con {-PAY-} (TyI (FS FZ)) Nil) Nil)
    FZ
    FZ
    Nil
    Nil
    (Con {-PAY-} (TyS (FS FZ)) Nil)
    (Struct {-PAY-} 12 (FS FZ) Nil Nil)

  $ Main 13
    (Con {-PAY-} (TyS (FS FZ)) Nil)
    (Struct {-PAY-} 14 (FS FZ) Nil Nil)
