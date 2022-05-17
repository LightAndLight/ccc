-- | The "Categorical Abstract Machine"
--
-- Cousineau, G., Curien, P. L., & Mauny, M. (1987). The categorical abstract machine. Science of computer programming, 8(2), 173-202.
module CAM where

import Control.Category ((>>>))
import ExprC (ExprC (..))
import Prelude hiding (abs, product)

uncons :: [a] -> Maybe (a, [a])
uncons [] = Nothing
uncons (x : xs) = Just (x, xs)

unsnoc :: [a] -> Maybe ([a], a)
unsnoc [] = Nothing
unsnoc [x] = Just ([], x)
unsnoc (x : xs) = (\(xs', y) -> (x : xs', y)) <$> unsnoc xs

data Value
  = VLam Value ExprC
  | VProduct [Value]
  | VInt Int
  deriving (Eq, Show)

(!) :: Value -> Int -> Value
(!) (VProduct ps) 0 = last ps
(!) v 0 = v
(!) (VProduct ps) n = VProduct (init ps) ! (n - 1)

snocV :: Value -> Value -> Value
snocV (VProduct ps) v = VProduct $ ps <> [v]
snocV v1 v2 = VProduct [v1, v2]

unsnocV :: Value -> Maybe (Value, Value)
unsnocV (VProduct ps) =
  (\(ps', v) -> (VProduct ps', v)) <$> unsnoc ps

data CAM = CAM {stack :: [Value], register :: Value}
  deriving (Eq, Show)

empty :: CAM
empty = CAM [] (VProduct [])

mapRegister :: (Value -> Value) -> CAM -> CAM
mapRegister f (CAM stk reg) = CAM stk (f reg)

push :: CAM -> CAM
push (CAM stk reg) =
  case unsnocV reg of
    Just (v, reg') -> CAM (v : stk) reg'
    Nothing -> undefined

pop :: CAM -> CAM
pop (CAM (v : stk) reg) =
  CAM stk (snocV v reg)

dup :: CAM -> CAM
dup = mapRegister (\reg -> VProduct [reg, reg])

swap :: CAM -> CAM
swap (CAM (v : stk) reg) = CAM (reg : stk) v

clear :: CAM -> CAM
clear = mapRegister (const $ VProduct [])

prj :: Int -> CAM -> CAM
prj ix = mapRegister (\reg -> reg ! ix)

int :: Int -> CAM -> CAM
int i = mapRegister (const $ VInt i)

add :: CAM -> CAM
add = mapRegister (\(VProduct [VInt x, VInt y]) -> VInt $ x + y)

mul :: CAM -> CAM
mul = mapRegister (\(VProduct [VInt x, VInt y]) -> VInt $ x * y)

abs :: ExprC -> CAM -> CAM
abs body = mapRegister (\reg -> VLam reg body)

product :: [CAM -> CAM] -> CAM -> CAM
product [] = clear
product [p] = p
product (p : ps) =
  -- register: X
  dup
    -- stack: s
    -- register: X * X
    >>> push
    -- stack: s, X
    -- register: X
    >>> p
    -- stack: s, X
    -- register: A
    >>> swap
    -- stack: s, A
    -- register: X
    >>> product ps
    -- stack: s, A
    -- register: B * C * ... * Z
    >>> pop

app :: CAM -> CAM
app state =
  let VProduct [VLam env body, x] = register state
   in run body (state {register = snocV env x})

run :: ExprC -> CAM -> CAM
run expr =
  case expr of
    IdC -> id
    ComposeC f g ->
      run f . run g
    ProductC ps ->
      product (run <$> ps)
    PrjC ix ->
      prj ix
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