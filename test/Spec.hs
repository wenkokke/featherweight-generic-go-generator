import Data.Coolean (toBool)
import qualified Data.Text.IO as T
import Language.FGG.Common
import Language.FGG.DeBruijn
import qualified Language.FGG.Named as N
import System.Exit (exitSuccess,exitFailure)


main :: IO ()
main | checkBools = exitSuccess
     | otherwise  = exitFailure

-- * Bools example from the paper

checkBools :: Bool
checkBools = toBool (checkProg bools)

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



-- * Bug found during the first test run

printBug1 :: IO ()
printBug1 = T.putStrLn $ N.prettyProg (convProg bug1)

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
