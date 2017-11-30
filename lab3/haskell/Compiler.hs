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

import System.Process (callProcess)
import System.FilePath.Posix (addExtension)

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
type Cxt = TODO
data TODO = TODO

-- | Labels.
newtype Label = L { theLabel :: Int }
  deriving (Eq, Enum)

-- | Empty state.
initSt :: St
initSt = St
  { cxt = TODO
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

  | Inc Type Addr Int -- ^ In/decrease variable by small number
  | Add Type         -- ^ Add 2 top values of stack.


-- | Entry point.

compile :: String -> Program -> IO ()
compile name prg@(PDefs defs) = do
  let sig = Map.fromList $
        builtin ++
        map (\ def@(DFun _ f@(Id x) _ _ ) -> (f, Fun (Id $ name ++ "/" ++ x) $ funType def)) defs
  let ((), w) = evalRWS (compileProgram name prg) sig initSt
  -- Print to stdout.
  mapM_ putStrLn w
  -- Write to .j file and call jasmin
  let jfile = addExtension name "j"
  writeFile jfile $ unlines w
  callProcess "jasmin" [jfile]

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
  put initSt{ nextLabel = lab }
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

    s -> nyi s

-- | Compiling and expression.

compileExp :: Exp -> Compile ()
compileExp = \case

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

    EApp f es -> do
      mapM_ compileExp es
      sig <- ask
      let Just fun = Map.lookup f sig
      emit (Call fun)


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

instance ToJVM Code where
  toJVM c = case c of

    Store t n -> prefix t ++ "store " ++ show n
    Load  t n -> prefix t ++ "load " ++ show n

    Pop t     -> "pop" ++ suffix t
    Return t  -> prefix t ++ "return"
    Call f    -> "invokestatic " ++ toJVM f

    IConst i  -> "ldc " ++ show i

    Add t        -> prefix t ++ "add"

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
  [ (Id "printInt"   , Fun (Id "Runtime/printInt"   ) $ FunType Type_void [Type_int])
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
newVar x t = fail $ "TODO: newVar"

-- | Return address and type of variable.
lookupVar :: Id -> Compile (Addr, Type)
lookupVar x = fail $ "TODO: lookupVar"

-- | Not yet implemented.

nyi :: Print a => a -> b
nyi t = error $ "Not yet implemented: compilation of: " ++ printTree t
