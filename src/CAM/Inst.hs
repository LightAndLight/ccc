-- | The Categorical Abstract Machine with state transitions reified into instructions.
--
-- This is the "bytecode" for the "categorical virtual machine".
module CAM.Inst where

import CAM (unsnoc)
import ExprC (ExprC (..))
import Prelude hiding (abs, product)

data Inst
  = PUSH
  | POP
  | DUP
  | SWAP
  | CLEAR
  | PRJ Int
  | ABS [Inst]
  | APP
  | INT Int
  | ADD
  | MUL
  deriving (Eq, Show)

product :: [ExprC] -> [Inst]
product [] = [CLEAR]
product [p] = compile p
product (p : ps) =
  [DUP, PUSH]
    <> compile p
    <> [SWAP]
    <> product ps
    <> [POP]

compile :: ExprC -> [Inst]
compile expr =
  case expr of
    IdC -> []
    ComposeC f g ->
      compile g <> compile f
    ProductC ps ->
      product ps
    PrjC ix ->
      [PRJ ix]
    AbsC body ->
      [ABS $ compile body]
    AppC ->
      [APP]
    IntC i ->
      [INT i]
    AddC ->
      [ADD]
    MulC ->
      [MUL]

data Value
  = VLam Value [Inst]
  | VPair Value [Value]
  | VUnit
  | VInt Int
  deriving (Eq, Show)

(!) :: Value -> Int -> Value
(!) (VPair v1 vs) 0 = last $ v1 : vs
(!) v 0 = v
(!) (VPair v1 vs) n = VPair v1 (init vs) ! (n - 1)

snocV :: Value -> Value -> Value
snocV (VPair v1 vs) v2 = VPair v1 (vs <> [v2])
snocV v1 v2 = VPair v1 [v2]

unsnocV :: Value -> Maybe (Value, Value)
unsnocV (VPair v1 vs) =
  case unsnoc vs of
    Nothing -> Just (VUnit, v1)
    Just (vs', x) -> Just (VPair v1 vs', x)

data CAM = CAM {stack :: [Value], register :: Value}
  deriving (Eq, Show)

empty :: CAM
empty = CAM [] VUnit

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
dup = mapRegister (\reg -> snocV reg reg)

swap :: CAM -> CAM
swap (CAM (v : stk) reg) = CAM (reg : stk) v

clear :: CAM -> CAM
clear = mapRegister (const VUnit)

prj :: Int -> CAM -> CAM
prj ix = mapRegister (\reg -> reg ! ix)

int :: Int -> CAM -> CAM
int i = mapRegister (const $ VInt i)

add :: CAM -> CAM
add = mapRegister (\(VPair (VInt x) [VInt y]) -> VInt $ x + y)

mul :: CAM -> CAM
mul = mapRegister (\(VPair (VInt x) [VInt y]) -> VInt $ x * y)

abs :: [Inst] -> CAM -> CAM
abs body = mapRegister (\reg -> VLam reg body)

app :: CAM -> CAM
app state =
  let VPair (VLam env body) [x] = register state
   in runInsts body (state {register = snocV env x})

runInst :: Inst -> CAM -> CAM
runInst inst =
  case inst of
    PUSH -> push
    POP -> pop
    DUP -> dup
    SWAP -> swap
    CLEAR -> clear
    PRJ ix -> prj ix
    ABS body -> abs body
    APP -> app
    INT i -> int i
    ADD -> add
    MUL -> mul

runInsts :: [Inst] -> CAM -> CAM
runInsts [] = id
runInsts (inst : insts) = runInsts insts . runInst inst