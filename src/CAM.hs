-- | The "Categorical Abstract Machine"
--
-- Cousineau, G., Curien, P. L., & Mauny, M. (1987). The categorical abstract machine. Science of computer programming, 8(2), 173-202.
module CAM where

import Control.Category ((>>>))
import ExprC (ExprC (..))
import Prelude hiding (abs, fst, snd)

data Value
  = VLam Value ExprC
  | VPair Value Value
  | VUnit
  | VInt Int
  deriving (Eq, Show)

data CAM = CAM {stack :: [Value], register :: Value}
  deriving (Eq, Show)

empty :: CAM
empty = CAM [] VUnit

mapRegister :: (Value -> Value) -> CAM -> CAM
mapRegister f (CAM stk reg) = CAM stk (f reg)

push :: CAM -> CAM
push (CAM stk (VPair v reg)) =
  CAM (v : stk) reg

pop :: CAM -> CAM
pop (CAM (v : stk) reg) =
  CAM stk (VPair v reg)

dup :: CAM -> CAM
dup = mapRegister (\reg -> VPair reg reg)

swap :: CAM -> CAM
swap (CAM (v : stk) reg) = CAM (reg : stk) v

clear :: CAM -> CAM
clear = mapRegister (const VUnit)

int :: Int -> CAM -> CAM
int i = mapRegister (const $ VInt i)

add :: CAM -> CAM
add = mapRegister (\(VPair (VInt x) (VInt y)) -> VInt $ x + y)

mul :: CAM -> CAM
mul = mapRegister (\(VPair (VInt x) (VInt y)) -> VInt $ x * y)

abs :: ExprC -> CAM -> CAM
abs body = mapRegister (\reg -> VLam reg body)

pair :: (CAM -> CAM) -> (CAM -> CAM) -> CAM -> CAM
pair a b =
  -- register: X
  dup
    -- stack: s
    -- register: X * X
    >>> push
    -- stack: s, X
    -- register: X
    >>> a
    -- stack: s, X
    -- register: A
    >>> swap
    -- stack: s, A
    -- register: X
    >>> b
    -- stack: s, A
    -- register: B
    >>> pop

fst :: CAM -> CAM
fst = mapRegister (\(VPair a _) -> a)

snd :: CAM -> CAM
snd = mapRegister (\(VPair _ b) -> b)

app :: CAM -> CAM
app state =
  let VPair (VLam env body) x = register state
   in run body (state {register = VPair env x})

run :: ExprC -> CAM -> CAM
run expr =
  case expr of
    IdC -> id
    ComposeC f g ->
      run f . run g
    TermC ->
      clear
    PairC a b ->
      pair (run a) (run b)
    FstC ->
      fst
    SndC ->
      snd
    AbsC body ->
      abs body
    AppC ->
      app
    IntC i ->
      int i
    AddC ->
      add
    MulC ->
      mul