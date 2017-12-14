{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Compiler where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.RWS

import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map

import System.Process (callProcess, callCommand)
import System.FilePath.Posix (addExtension)
import System.FilePath (takeFileName, takeDirectory)

import Ann.Abs
import Ann.Print

-- | Compilation monad.
type Compile = RWS Sig Output St

-- | Read-only state of compiler.
type Sig = Map Id Fun

-- | Function names bundled with their type.
data Fun = Fun
  { funId      :: Id
  , funFunType :: FunType
  }

data FunType = FunType Type [Type]

-- | Mutable state of compiler.
data St = St
  { cxt           :: Cxt   -- ^ Context.
  , limitLocals   :: Int   -- ^ Maximal size for locals encountered.
  , currentStack  :: Int   -- ^ Current stack size.
  , limitStack    :: Int   -- ^ Maximal stack size encountered.
  , nextLabel     :: Label -- ^ Next jump label (persistent part of state)
  }

-- | Variable contexts.
type Cxt = [Map Id Var]
type Var = (Addr, Type)

-- | Labels.
newtype Label = L { theLabel :: Int }
  deriving (Eq, Enum)

instance Show Label where
    show (L i) = "l" ++ show i

-- | Empty state.
initSt :: St
initSt = St
  { cxt = [Map.empty]
  , limitLocals   = 0
  , currentStack  = 0
  , limitStack    = 0
  , nextLabel     = L 0
  }

-- | Output of the compiler (.j file).
type Output = [String]

type Addr = Int

-- | JVM instructions.
data Code
  = Store Type Addr  -- ^ Store stack content of type @Type@ in local variable @Addr@.
  | Load  Type Addr  -- ^ Push stack content of type @Type@ from local variable @Addr@.
  | IConst Integer   -- ^ Put integer constant on the stack.

  | Pop Type         -- ^ Drop top stack element of type @Type@.
  | Return Type      -- ^ Return from method of type @Type@.
  | Call Fun         -- ^ Call function.
  | Dup

  -- | Inc Type Addr Int -- ^ In/decrease variable by small number
  | Add Type         -- ^ Add 2 top values of stack.
  | Sub Type
  | Mul Type
  | Div Type

  | IfEq Label
  | IfLt Label
  | IfCmpEq Label
  | IfCmpLt Label
  | IfCmpLe Label
  | IfLte Label
  | IfGt Label
  | IfGte Label
  | GoTo Label

  | Lab Label

-- | Entry point.

compile :: String -> Program -> IO ()
compile name prg@(PDefs defs) = do
  let sig = Map.fromList $
        builtin ++
        map (\ def@(DFun _ f@(Id x) _ _ ) -> (f, Fun (Id $ (takeFileName name) ++ "/" ++ x) $ funType def)) defs
  let ((), w) = evalRWS (compileProgram (takeFileName name) prg) sig initSt
  -- Print to stdout.
  mapM_ putStrLn w
  -- Write to .j file and call jasmin
  let jfile = addExtension name "j"
  writeFile jfile $ unlines w
  callCommand ("jasmin -d " ++ (takeDirectory name) ++ " " ++ jfile)

-- | Compiling the program.

compileProgram :: String -> Program -> Compile ()
compileProgram name (PDefs defs) = do
  tell header
  mapM_ compileFun defs
  where
  header =
    [ ";; BEGIN HEADER"
    , ""
    , ".class public " ++ name
    , ".super java/lang/Object"
    , ""
    , ".method public <init>()V"
    , "  .limit locals 1"
    , ""
    , "  aload_0"
    , "  invokespecial java/lang/Object/<init>()V"
    , "  return"
    , ""
    , ".end method"
    , ""
    , ".method public static main([Ljava/lang/String;)V"
    , "  .limit locals 1"
    , "  .limit stack  1"
    , ""
    , "  invokestatic " ++ name ++ "/main()I"
    , "  pop"
    , "  return"
    , ""
    , ".end method"
    , ""
    , ";; END HEADER"
    ]

-- | Compiling a function definition.

compileFun :: Def -> Compile ()
compileFun def@(DFun t f args ss) = do
  -- function header
  tell [ "", ".method public static " ++ toJVM (Fun f $ funType def) ]

  -- prepare environment
  lab <- gets nextLabel
  put initSt{nextLabel = lab}
  mapM_ (\ (ADecl t' x) -> newVar x t') args

  -- compile statements
  w <- grabOutput $ do
    mapM_ compileStm ss

  -- output limits
  ll <- gets limitLocals
  ls <- gets limitStack
  tell [ "  .limit locals " ++ show ll
       , "  .limit stack  " ++ show ls
       ]

  -- output code, indented by 2
  tell $ map (\ s -> if null s then s else "  " ++ s) w
  tell ["  return"]
  -- function footer
  tell [ "", ".end method"]


-- | Compiling a statement.

compileStm :: Stm -> Compile ()
compileStm s = do

  -- Compile statement
  case s of

    SExp t e -> do
      compileExp e
      emit (Pop t)

    SReturn t e -> do
      compileExp e
      emit (Return t)

    SInit t x e -> do
      newVar x t
      compileExp e
      (a, _) <- lookupVar x
      emit (Store t a)

    SDecls t ids -> do
      mapM_ (\id -> newVar id t) ids

    SWhile exp stm -> do
        test <- getLabel
        end <- getLabel
        emit (Lab test)
        compileExp exp
        emit (IfEq end)
        compileStm stm
        emit (GoTo test)
        emit (Lab end)


    SBlock stms -> do
        newBlock
        mapM_ compileStm stms
        exitBlock

    SIfElse exp stm1 stm2 -> do
        ifLabel <- getLabel
        elseLabel <- getLabel
        compileExp exp
        emit (IfEq elseLabel)
        compileStm stm1
        emit (GoTo ifLabel)
        emit (Lab elseLabel)
        compileStm stm2
        emit (Lab ifLabel)

-- | Compiling and expression.

compileExp :: Exp -> Compile ()
compileExp = \case
    ETrue  -> emit (IConst 1)
    EFalse -> emit (IConst 0)
    EInt i -> do
      emit (IConst i)

    EId x -> do
      (a, t) <- lookupVar x
      emit (Load t a)

    EPreIncr x -> do
      (a, t) <- lookupVar x
      emit (Load t a)
      emit (IConst 1)
      emit (Add t)
      emit (Store t a)
      emit (Load t a)

    EPreDecr x -> do
      (a, t) <- lookupVar x
      emit (Load t a)
      emit (IConst 1)
      emit (Sub t)
      emit (Store t a)
      emit (Load t a)

    EPostIncr x -> do
      (a, t) <- lookupVar x
      emit (Load t a)
      emit Dup
      emit (IConst 1)
      emit (Add t)
      emit (Store t a)

    EPostDecr x -> do
      (a, t) <- lookupVar x
      emit (Load t a)
      emit Dup
      emit (IConst 1)
      emit (Sub t)
      emit (Store t a)

    EApp f es -> do
      mapM_ compileExp es
      sig <- ask
      let Just fun = Map.lookup f sig
      emit (Call fun)

    EDiv t exp1 exp2 -> do
      compileExp exp1
      compileExp exp2
      emit (Div t)

    ETimes t exp1 exp2 -> do
      compileExp exp1
      compileExp exp2
      emit (Mul t)

    EPlus t exp1 exp2 -> do
      compileExp exp1
      compileExp exp2
      emit (Add t)

    EMinus t exp1 exp2 -> do
      compileExp exp1
      compileExp exp2
      emit (Sub t)

    ELt t exp1 exp2 -> do
        true <- getLabel
        end  <- getLabel
        compileExp exp1
        compileExp exp2
        emit (IfCmpLt true)
        emit (IConst 0)
        emit (GoTo end)
        emit (Lab true)
        emit (IConst 1)
        emit (Lab end)


    EGt t exp1 exp2 -> do
        true <- getLabel
        end  <- getLabel
        compileExp exp2
        compileExp exp1
        emit (IfCmpLt true)
        emit (IConst 0)
        emit (GoTo end)
        emit (Lab true)
        emit (IConst 1)
        emit (Lab end)

    ELtEq t exp1 exp2 -> do
        true <- getLabel
        end  <- getLabel
        compileExp exp1
        compileExp exp2
        emit (IfCmpLe true)
        emit (IConst 0)
        emit (GoTo end)
        emit (Lab true)
        emit (IConst 1)
        emit (Lab end)

    EGtEq t exp1 exp2 -> do
        true <- getLabel
        end  <- getLabel
        compileExp exp2
        compileExp exp1
        emit (IfCmpLe true)
        emit (IConst 0)
        emit (GoTo end)
        emit (Lab true)
        emit (IConst 1)
        emit (Lab end)

    EEq t exp1 exp2 -> do
        true <- getLabel
        end  <- getLabel
        compileExp exp1
        compileExp exp2
        emit (IfCmpEq true)
        emit (IConst 0)
        emit (GoTo end)
        emit (Lab true)
        emit (IConst 1)
        emit (Lab end)

    ENEq t exp1 exp2 -> do
        true <- getLabel
        end  <- getLabel
        compileExp exp1
        compileExp exp2
        emit (IfCmpEq true)
        emit (IConst 1)
        emit (GoTo end)
        emit (Lab true)
        emit (IConst 0)
        emit (Lab end)

    EAnd exp1 exp2 -> do
        compileExp exp1
        false <- getLabel
        end  <- getLabel
        emit (IfEq false)
        compileExp exp2
        emit (GoTo end)
        emit (Lab false)
        emit (IConst 0)
        emit (Lab end)

    EOr exp1 exp2 -> do
        compileExp exp1
        false <- getLabel
        end  <- getLabel
        emit (IfEq false)
        emit (IConst 1)
        emit (GoTo end)
        emit (Lab false)
        compileExp exp2
        emit (Lab end)

    EAss (EId id) exp2 -> do
        compileExp exp2
        emit Dup
        (a, t) <- lookupVar id
        emit (Store t a)

    e -> nyi e

---------------------------------------------------------------------------
-- * Code emission
---------------------------------------------------------------------------

-- | Print a single instruction.  Also update stack limits
emit :: Code -> Compile ()

-- Handling of void

emit (Store Type_void _) = return ()
emit (Load  Type_void _) = return ()
emit (Pop   Type_void  ) = return ()

emit c = do
  tell [toJVM c]
  -- Adjust stack
  case c of
    Store t _ -> decStack t
    Load  t _ -> incStack t
    IConst _  -> incStack Type_int
    Pop    t  -> decStack t
    Return t  -> decStack t
    Call f    -> decStack f
    Add t     -> decStack t
    Sub t     -> decStack t
    Mul t     -> decStack t
    Div t     -> decStack t
    Dup       -> incStack Type_int
    s         -> return ()

instance ToJVM Code where
  toJVM c = case c of

    Store t n -> prefix t ++ "store " ++ show n
    Load  t n -> prefix t ++ "load " ++ show n

    Pop t     -> "pop" ++ suffix t
    Return t  -> prefix t ++ "return"
    Call f    -> "invokestatic " ++ toJVM f
    Dup       -> "dup"

    IConst i  -> "ldc " ++ show i

    Add t     -> prefix t ++ "add"
    Sub t     -> prefix t ++ "sub"
    Mul t     -> prefix t ++ "mul"
    Div t     -> prefix t ++ "div"

    Lab l     -> show l ++ ":"
    IfEq l    -> "ifeq " ++ show l
    IfLt l    -> "iflt " ++ show l
    IfLte l   -> "ifle " ++ show l
    IfGt l    -> "ifgt " ++ show l
    IfGte l   -> "ifge " ++ show l
    GoTo l    -> "goto " ++ show l

    IfCmpEq l -> "if_icmpeq " ++ show l
    IfCmpLt l -> "if_icmplt " ++ show l
    IfCmpLe l -> "if_icmple " ++ show l

-- | Type-prefix for JVM instructions.
prefix :: Type -> String
prefix t = case t of
  Type_double -> "d"
  Type_int    -> "i"
  Type_bool   -> "i"
  Type_void   -> ""

-- | Type-prefix for JVM instructions.
suffix :: Type -> String
suffix t = case t of
  Type_double -> "2"
  _ -> ""

-- | Get the output from the monad.

grabOutput :: Compile () -> Compile Output
grabOutput m = do
  r <- ask
  s <- get
  let ((), s', w) = runRWS m r s
  put s'
  return w

---------------------------------------------------------------------------
-- ** Stack limit computation
---------------------------------------------------------------------------

-- | Compute the number of machine words in something

class Size a where
  size :: a -> Int

instance Size Type where
  size t = case t of
    Type_int    -> 1
    Type_double -> 2
    Type_bool   -> 1
    Type_void   -> 0

instance Size FunType where
  size (FunType t ts) = sum (map size ts) - size t

instance Size Fun where
  size (Fun _ ft) = size ft

-- | Stack size modification.
modStack :: Int -> Compile ()
modStack n = do
  new <- (n +) <$> gets currentStack
  modify $ \ st -> st { currentStack = new }
  old <- gets limitStack
  when (new > old) $
    modify $ \ st -> st { limitStack = new }

-- | Increase the current stack size to fit element of given type.
incStack :: Size t => t -> Compile ()
incStack t = modStack (size t)

-- | Note: @size t@ can be negative,
--   thus, @decStack@ can also increase the stack limit.
decStack :: Size t => t -> Compile ()
decStack t = modStack (0 - size t)

---------------------------------------------------------------------------
-- * Functions and Signature
---------------------------------------------------------------------------

-- | Builtin-functions
builtin :: [(Id, Fun)]
builtin =
  [ (Id "printInt"   , Fun (Id "Runtime/printInt"   ) $ FunType Type_void [Type_int]),
    (Id "readInt"    , Fun (Id "Runtime/readInt"    ) $ FunType Type_int [])
  ]
  -- TODO: more functions

-- | Turn a Def into a function type.
funType :: Def -> FunType
funType (DFun t _ args _) = FunType t $ map (\ (ADecl t' _) -> t') args

-- | Print something in jasmin-syntax
class ToJVM a where
  toJVM :: a -> String

instance ToJVM Type where
  toJVM t = case t of
    Type_int    -> "I"
    Type_void   -> "V"
    Type_double -> "D"
    Type_bool   -> "Z"

instance ToJVM FunType where
  toJVM (FunType t ts) = "(" ++ (toJVM =<< ts) ++ ")" ++ toJVM t

instance ToJVM Fun where
  toJVM (Fun (Id f) t) = f ++ toJVM t

instance ToJVM Label where
  toJVM (L l) = "L" ++ show l

---------------------------------------------------------------------------
-- * Variable handling
---------------------------------------------------------------------------

newVar :: Id -> Type -> Compile ()
newVar x t = do
    c:cs <- gets cxt
    L i <- getLabel
    ll <- gets limitLocals
    modify $ \ st -> st {cxt = ((Map.insert x (i, t) c ):cs),
                         limitLocals = ll + 1}


-- | Return address and type of variable.
lookupVar :: Id -> Compile (Addr, Type)
lookupVar x = do
    cs <- gets cxt
    case lookupVar' x cs of
        Just(addr, typ) -> return (addr, typ)
        Nothing -> fail "No such variable"

lookupVar' :: Id -> Cxt -> Maybe (Addr, Type)
lookupVar' id [] = Nothing
lookupVar' id (c:cs) = case Map.lookup id c of
    Just(addr, typ) -> return (addr, typ)
    Nothing -> lookupVar' id cs

-- | Not yet implemented.

nyi :: Print a => a -> b
nyi t = error $ "Not yet implemented: compilation of: " ++ printTree t


getLabel :: Compile (Label)
getLabel = do
    (L nexLabel) <- gets nextLabel
    modify $ \ st -> st {nextLabel = (L (nexLabel + 1))}
    return (L nexLabel)

newBlock :: Compile ()
newBlock = do
    con <- gets cxt
    modify $ \ st -> st {cxt = (Map.empty:con)}

exitBlock :: Compile ()
exitBlock = do
    (c:con) <- gets cxt
    modify $ \ st -> st {cxt = con}
