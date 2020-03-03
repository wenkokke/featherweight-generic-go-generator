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
  $ NewM 3
  $ TyDecls 4
  -- type TT struct {};
  $ LetStruct 5 Nil Nil
  -- type FF struct {};
  $ LetStruct 6 Nil Nil
  -- type Bool interface { Not() Bool };
  $ LetInterface 7
    Nil
    Nil
    (Cons (FZ, MSig Nil (TyI FZ) Nil (Con (TyI FZ) Nil)) Nil)
  $ TmDecls 8
  -- func (this TT) Not() { return FF };
  $ LetMethod 9
    Nil
    FZ
    FZ
    Nil
    Nil
    (Con (TyS FZ) Nil)
    (Struct 10 (FS FZ) Nil Nil)
  -- func (this FF) Not() { return TT };
  $ LetMethod 11
    Nil
    (FS FZ)
    FZ
    Nil
    Nil
    (Con (TyS (FS FZ)) Nil)
    (Struct 12 FZ Nil Nil)
  -- func main() { _ = TT.Not() };
  $ Main 13
  (Con (TyS FZ) Nil)
  (Call 14
    (Struct 15 (FS FZ) Nil Nil)
    (Con (TyS (FS FZ)) Nil)
    FZ
    Nil
    Nil)
