{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Unrestricted.SSA where

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.Hashable (Hashable)
import Data.List (intercalate)
import Debug.Trace (traceShow, traceShowId)
import Unrestricted (ExprC (..))

newtype Local = Local Int
  deriving (Eq, Show)

newtype Global = Global String
  deriving (Eq, Show, Hashable)

data Value
  = Var Local
  | Pair Value Value
  | Unit
  | Closure Value Global
  | Int Int
  deriving (Eq, Show)

data Inst
  = Call {result :: Local, arg1 :: Value, arg2 :: Value}
  | Add {result :: Local, arg1 :: Value, arg2 :: Value}
  | Mul {result :: Local, arg1 :: Value, arg2 :: Value}
  | Dup {left :: Local, right :: Local, arg :: Value}
  | Drop {arg :: Value}
  deriving (Eq, Show)

data Block = Block
  { body :: [Inst],
    ret :: Value
  }
  deriving (Show)

data Def = Def
  { name :: Global,
    params :: Int,
    block :: Block
  }
  deriving (Show)

data SSA = SSA
  { locals :: Int,
    defs :: HashMap Global Def,
    insts :: [Inst],
    val :: Value
  }
  deriving (Show)

showSSA :: SSA -> String
showSSA ssa =
  unlines $
    [ "locals: " <> show (locals ssa),
      "",
      "defs:",
      ""
    ]
      <> foldr
        ( \(Def (Global name) params block) rest ->
            ("@" <> name <> "(" <> showParams params <> ")" <> "{") :
            fmap ("  " <>) (showBlock block)
              <> ["}", ""]
              <> rest
        )
        []
        (defs ssa)
      <> ["insts:", ""]
      <> fmap showInst (insts ssa)
      <> ["val: " <> show (val ssa)]
  where
    showValue (Var (Local a)) = "%" <> show a
    showValue Unit = "()"
    showValue (Pair a b) = "(" <> showValue a <> ", " <> showValue b <> ")"
    showValue (Int i) = show i
    showValue (Closure a (Global b)) = "Closure(" <> showValue a <> ", @" <> b <> ")"

    showInst inst =
      case inst of
        Add (Local res) a b ->
          "%" <> show res <> " = add(" <> showValue a <> ", " <> showValue b <> ")"
        Mul (Local res) a b ->
          "%" <> show res <> " = mul(" <> showValue a <> ", " <> showValue b <> ")"
        Call (Local res) a b ->
          "%" <> show res <> " = call(" <> showValue a <> ", " <> showValue b <> ")"
        Dup (Local res1) (Local res2) a ->
          "%" <> show res1 <> ", " <> "%" <> show res2 <> " = dup(" <> showValue a <> ")"
        Drop a ->
          "drop(" <> showValue a <> ")"

    showBlock (Block insts ret) = (showInst <$> insts) <> ["ret " <> showValue ret]

    showParams n = intercalate ", " $ ("%" <>) . show <$> [0 .. n - 1]

empty :: SSA
empty = SSA {locals = 0, defs = mempty, insts = mempty, val = Unit}

compile :: ExprC -> SSA -> SSA
compile expr state =
  case expr of
    IdC -> state
    ComposeC f g ->
      (compile f . compile g) state
    ForgetlC ->
      let Pair Unit value = val state
       in state {val = value}
    ForgetrC ->
      let Pair value Unit = val state
       in state {val = value}
    UnforgetlC ->
      state {val = Pair Unit $ val state}
    UnforgetrC ->
      state {val = Pair (val state) Unit}
    AssoclC ->
      let Pair a (Pair b c) = val state
       in state {val = Pair (Pair a b) c}
    AssocrC ->
      let Pair (Pair a b) c = val state
       in state {val = Pair a (Pair b c)}
    SwapC ->
      let Pair a b = val state
       in state {val = Pair b a}
    ParC f g ->
      let Pair a b = val state
          state' = compile f (state {val = a})
          state'' = compile g (state' {val = b})
       in state'' {val = Pair (val state') (val state'')}
    DupC ->
      let value = val state
          n = locals state
          left = Local n
          right = Local $ n + 1
       in case value of
            Var _ ->
              state
                { locals = n + 2,
                  insts = insts state <> [Dup left right $ val state],
                  val = Pair (Var left) (Var right)
                }
            _ ->
              state {val = Pair value value}
    TermC ->
      state
        { insts = insts state <> [Drop $ val state],
          val = Unit
        }
    AbsC body ->
      let funcName = Global $ "closure_code_" <> show (length $ defs state)

          countLocals Unit = 0
          countLocals (Pair a b) = countLocals a + 1

          numParams = countLocals (val state) + 1

          SSA _locals defs' insts returnVal =
            compile
              body
              empty
                { locals = numParams,
                  defs = HashMap.insert funcName undefined $ defs state,
                  val = foldl (\l -> Pair l . Var . Local) Unit [0 .. numParams - 1]
                }
       in state
            { defs = HashMap.insert funcName (Def funcName numParams $ Block insts returnVal) defs',
              val = Closure (val state) funcName
            }
    AppC ->
      let Pair a b = val state
          name = Local $ locals state
       in state
            { locals = locals state + 1,
              insts = insts state <> [Call name a b],
              val = Var name
            }
    IntC i ->
      state {val = Int i}
    AddC ->
      let Pair a b = val state
          name = Local $ locals state
       in state
            { locals = locals state + 1,
              insts = insts state <> [Add name a b],
              val = Var name
            }
    MulC ->
      let Pair a b = val state
          name = Local $ locals state
       in state
            { locals = locals state + 1,
              insts = insts state <> [Mul name a b],
              val = Var name
            }