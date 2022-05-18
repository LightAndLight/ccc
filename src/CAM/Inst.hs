-- | The Categorical Abstract Machine with state transitions reified into instructions.
--
-- This is the "bytecode" for the "categorical virtual machine".
module CAM.Inst where

import Debug.Trace (traceShow)
import ExprC (ExprC (..))
import Prelude hiding (abs, fst, snd)

data Inst
  = PUSH
  | POP
  | DUP
  | SWAP
  | CLEAR
  | FST
  | SND
  | ABS [Inst]
  | APP
  | INT Int
  | ADD
  | MUL
  deriving (Eq, Show)

pair :: ExprC -> ExprC -> [Inst]
pair a b =
  [DUP, PUSH]
    <> compile a
    <> [SWAP]
    <> compile b
    <> [POP]

compile :: ExprC -> [Inst]
compile expr =
  case expr of
    IdC -> []
    ComposeC f g ->
      compile g <> compile f
    TermC ->
      [CLEAR]
    PairC a b ->
      pair a b
    FstC ->
      [FST]
    SndC ->
      [SND]
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

fst :: CAM -> CAM
fst = mapRegister (\(VPair a _) -> a)

snd :: CAM -> CAM
snd = mapRegister (\(VPair _ b) -> b)

int :: Int -> CAM -> CAM
int i = mapRegister (const $ VInt i)

add :: CAM -> CAM
add = mapRegister (\(VPair (VInt x) (VInt y)) -> VInt $ x + y)

mul :: CAM -> CAM
mul = mapRegister (\(VPair (VInt x) (VInt y)) -> VInt $ x * y)

abs :: [Inst] -> CAM -> CAM
abs body = mapRegister (\reg -> VLam reg body)

app :: CAM -> CAM
app state =
  let VPair (VLam env body) x = register state
   in runInsts body (state {register = VPair env x})

runInst :: Inst -> CAM -> CAM
runInst inst =
  case inst of
    PUSH -> push
    POP -> pop
    DUP -> dup
    SWAP -> swap
    CLEAR -> clear
    FST -> fst
    SND -> snd
    ABS body -> abs body
    APP -> app
    INT i -> int i
    ADD -> add
    MUL -> mul

runInsts :: [Inst] -> CAM -> CAM
runInsts [] = id
runInsts (inst : insts) = runInsts insts . runInst inst . (\env -> traceShow (inst, env) env)