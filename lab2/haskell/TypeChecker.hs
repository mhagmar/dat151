module TypeChecker where

import Control.Monad

import Env

import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM



typecheck :: Program -> Err ()
typecheck PDef (DFun dataType id args stms) =
typecheck p = return ()

checkStm :: Env -> Type -> Stm -> Err Env
checkStm env t SExp exp = case checkExp env t exp of
                            Ok    -> Ok t
                            Bad s -> Bad s
checkStm (sig, c) t1 SDecls t2 ids = Ok (update)


checkExp :: Env -> Type -> Exp -> Err ()
checkExp env t exp = do
    t2 <- inferExp env exp
    if (t2 == t) then
        return ()
    else
        fail $ "type of " ++ printTree exp ++
               "expected" ++ printTree t   ++
               "but found" ++ printTree t2

inferExp :: Env -> Exp -> Err Type
inferExp env ETrue        = Ok Type_bool
inferExp env EFalse       = Ok Type_bool
inferExp env (EInt       _) = Ok Type_int
inferExp env (EDouble    _) = Ok Type_double
inferExp env (EId       id) = lookupVar env id
inferExp env (EPostIncr id) = lookupVar env id
inferExp env (EPostDecr id) = lookupVar env id
inferExp env (EPreIncr  id) = lookupVar env id
inferExp env (EPreDecr  id) = lookupVar env id
inferExp env (EApp id exps) = case lookupFun env  id of
                                Ok (ts, t) -> f env ts exps t
                                Bad s   -> Bad s
inferExp env (ETimes e1 e2) = compareTypes env e1 e2
inferExp env (EDiv   e1 e2) = compareTypes env e1 e2
inferExp env (EPlus  e1 e2) = compareTypes env e1 e2
inferExp env (EMinus e1 e2) = compareTypes env e1 e2
inferExp env (ELt    e1 e2) = case compareTypes env e1 e2 of
                          Ok _  -> Ok Type_bool
                          Bad s -> Bad s
inferExp env (EGt    e1 e2) = case compareTypes env e1 e2 of
                          Ok _  -> Ok Type_bool
                          Bad s -> Bad s
inferExp env (ELtEq  e1 e2) = case compareTypes env e1 e2 of
                          Ok _  -> Ok Type_bool
                          Bad s -> Bad s
inferExp env (EGtEq  e1 e2) = case compareTypes env e1 e2 of
                          Ok _  -> Ok Type_bool
                          Bad s -> Bad s
inferExp env (EEq    e1 e2) = case compareTypes env e1 e2 of
                          Ok _  -> Ok Type_bool
                          Bad s -> Bad s
inferExp env (ENEq   e1 e2) = case compareTypes env e1 e2 of
                          Ok _  -> Ok Type_bool
                          Bad s -> Bad s
inferExp env (EAnd   e1 e2) = case compareTypes env e1 e2 of
                          Ok _  -> Ok Type_bool
                          Bad s -> Bad s
inferExp env (EOr    e1 e2) = case compareTypes env e1 e2 of
                          Ok _  -> Ok Type_bool
                          Bad s -> Bad s
inferExp env (EAss   id e1) = case lookupVar env id of
                            Ok t1 -> case inferExp env e1 of
                                    Ok t2 -> if t1 == t2 then Ok t1
                                                         else Bad "Type error"
                            Bad s -> Bad s


lookupVar :: Env -> Id -> Err Type
lookupVar (_, [])   id = Bad ("Variable " ++ show id ++ " not found")
lookupVar (sig, c:cs) id = case Map.lookup id c of
                            Just t -> Ok t
                            Nothing -> lookupVar (sig, cs) id

lookupFun :: Env -> Id -> Err ([Type], Type)
lookupFun (sig, _) id = case Map.lookup id sig of
                            Just (ts, t) -> Ok (ts, t)
                            Nothing -> Bad ("Variable " ++ show id ++ " not found")

updateVar :: Env -> Id -> Type -> Err Env
updateVar (sig, c:cs) id t = case Map.lookup id c of
                                Just t2 -> Bad "Fuxk off"
                                Nothing -> Ok $ (sig, (Map.insert id t c):cs)

updateFun :: Env -> Id -> ([Type], Type) -> Err Env
updateFun (sig, c) id (ts, t) = case Map.lookup id sig of
                                            Just (ts2, t2) -> Bad "Bugger off"
                                            Nothing -> Ok $ (Map.insert id (ts, t) sig, c)

newBlock  :: Env -> Env
newBlock (sig, cs) = (sig, Map.empty:cs)

emptyEnv  :: Env
emptyEnv = (Map.empty, Map.empty:[])

compareTypes :: Env -> Exp -> Exp -> Err Type
compareTypes env e1 e2 = case inferExp env e1 of
                         Ok t1 -> case inferExp env e2 of
                            Ok t2 -> if t1 == t2 then Ok t1
                                                 else Bad "Type error"
                            Bad s -> Bad s
                         Bad s -> Bad s

f :: Env -> [Type] -> [Exp] -> Type -> Err Type
f env []   []       t = Ok t
f env []   (y:ys)   t = Bad "Too few args@"
f env (x:xs) []     t = Bad "Too few args"
f env (x:xs) (y:ys) t = case checkExp env x y of
                            Ok _ -> f env xs ys t
                            Bad s -> Bad s