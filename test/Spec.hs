import Control.Monad (unless)
import Data.Coolean (toBool)
import Language.FGG.Common
import Language.FGG.DeBruijn
import System.Exit (exitFailure)

main :: IO ()
main =
  unless (toBool (checkProg bools)) exitFailure

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
