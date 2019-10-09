import Control.Monad (unless)
import Data.Coolean (toBool)
import Language.FGG.Common
import Language.FGG.DeBruijn
import System.Exit (exitFailure)

main :: IO ()
main = do
  unless (toBool (checkProg bools)) exitFailure

bools :: Prog
bools
  = FDecls
  $ MDecls
  $ NewM
  $ TyDecls
  -- type TT struct {};
  $ LetStruct Nil Nil
  -- type FF struct {};
  $ LetStruct Nil Nil
  -- type Bool interface { Not() Bool };
  $ LetInterface
    Nil
    Nil
    (Cons (FZ, MSig Nil (TyI FZ) Nil (Con (TyI FZ) Nil)) Nil)
  $ TmDecls
  -- func (this TT) Not() { return FF };
  $ LetMethod
    Nil
    FZ
    FZ
    Nil
    Nil
    (Con (TyS FZ) Nil)
    (Struct (FS FZ) Nil Nil)
  -- func (this FF) Not() { return TT };
  $ LetMethod
    Nil
    (FS FZ)
    FZ
    Nil
    Nil
    (Con (TyS (FS FZ)) Nil)
    (Struct FZ Nil Nil)
  -- func main() { _ = TT.Not() };
  $ Main
  (Con (TyS FZ) Nil)
  (Call
    (Struct (FS FZ) Nil Nil)
    (Con (TyS (FS FZ)) Nil)
    FZ
    Nil
    Nil)
