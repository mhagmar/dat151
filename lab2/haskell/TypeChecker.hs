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

check :: Env -> Exp -> Err Type
check env ETrue        = Ok Type_bool
check env EFalse       = Ok Type_bool
check env EInt       _ = Ok Type_int
check env EDouble    _ = Ok Type_double
check env EId       id = case snd(lookup(id)) of
                        Ok e -> check env e
                        Bad s -> Bad s
check env EApp      id = case snd(lookup(id)) of
                        Ok e -> check env e
                        Bad s -> Bad s
check env EPostIncr id = case snd(lookup(id)) of
                        Ok e -> check env e
                        Bad s -> Bad s
check env EPostDecr id = case snd(lookup(id)) of
                        Ok e -> check env e
                        Bad s -> Bad s
check env EPreIncr  id = case snd(lookup(id)) of
                        Ok e -> check env e
                        Bad s -> Bad s
check env EPreDecr  id = case snd(lookup(id)) of
                        Ok e -> check env e
                        Bad s -> Bad s
check env ETimes e1 e2 = case check env e1 of  -- Perhaps we need to infer type here instead since we could have 1 * 1.0
                        Ok t1 -> case check env e2 of
                            Ok t2 -> if t1 == t2 then Ok t1
                                                    else Bad "Type t1 cannot be multiplied with type t2"
                            Bad s -> Bad s
                        Bad s -> Bad s
check env EDiv   e1 e2 = case check env e1 of
                        Ok t1 -> case check e2 of
                            Ok t2 -> if t1 == t2 then Ok t1
                                                    else Bad "Type t1 cannot be dived by type t2"
                            Bad s -> Bad s
                        Bad s -> Bad s
check env EPlus  e1 e2 = case check env e1 of
                        Ok t1 -> case check env e2 of
                            Ok t2 -> if t1 == t2 then Ok t1
                                                    else Bad "Type t1 connot be added to type t2"
                            Bad s -> Bad s
                        Bad s -> Bad s
check env EMinus e1 e2 = case check env e1 of
                        Ok t1 -> case check env e2 of
                            Ok t2 -> if t1 == t2 then Ok t1
                                                    else Bad "Type t1 cannot be subtracted from type t2"
                            Bad s -> Bad s
                        Bad s -> Bad s
check env ELt    e1 e2 = infer env (ELt   e1 e2) -- should probably be some check here that e1 and e2 are comparable
check env EGt    e1 e2 = infer env (EGt   e1 e2)
check env ELtEq  e1 e2 = infer env (ELtEq e1 e2)
check env EGtEq  e1 e2 = infer env (EGtEq e1 e2)
check env EEq    e1 e2 = infer env (EEq   e1 e2)
check env ENEq   e1 e2 = infer env (ENEq  e1 e2)
check env EAnd   e1 e2 = infer env (EAnd  e1 e2)
check env EOr    e1 e2 = infer (EOr   e1 e2)
check env EAss   id e1 = case snd(lookup(id)) of -- Not sure, perhaps just return the type of the righthand expr but check that that is the expression of the left hand
                        Ok e -> check env e
                        Bad s -> raise error

infer :: Env -> Exp -> Maybe Type  -- Many of these might not be needed
infer env ETrue        = Ok Type_bool
infer env EFalse       = Ok Type_bool
infer env EInt       _ = Ok Type_int
infer env EDouble    _ = Ok Type_double
infer env EId       id = case snd(lookup(id)) of
                        Ok e -> check env e
                        Bad s -> Bad s
infer env EApp      id = case snd(lookup(id)) of
                        Ok e -> check env e
                        Bad s -> Bad s
infer env EPostIncr id = case snd(lookup(id)) of
                        Ok e -> check env e
                        Bad s -> Bad s
infer env EPostDecr id = case snd(lookup(id)) of
                        Ok e -> check env e
                        Bad s -> Bad s
infer env EPreIncr  id = case snd(lookup(id)) of
                        Ok e -> check env e
                        Bad s -> Bad s
infer env EPreDecr  id = case snd(lookup(id)) of
                        Ok e -> check env e
                        Bad s -> Bad s
infer env ETimes e1 e2 = case check env e1 of  -- Perhaps we need to infer type here instead since we could have 1 * 1.0
                        Ok t1 -> case check env e2 of
                            Ok t2 -> if t1 == t2 then Ok t1
                                                    else fail
                            Bad s -> Bad s
                        Bad s -> Bad s
infer env EDiv   e1 e2 = case check env e1 of
                        Ok t1 -> case check env e2 of
                            Ok t2 -> if t1 == t2 then Ok t1
                                                    else fail
                            Bad s -> Bad s
                        Bad s -> Bad s
infer env EPlus  e1 e2 = case check env e1 of
                        Ok t1 -> case check env e2 of
                            Ok t2 -> if t1 == t2 then Ok t1
                                                    else fail
                            Bad s -> Bad s
                        Bad s -> Bad s
infer env EMinus e1 e2 = case check env e1 of
                        Ok t1 -> case check env e2 of
                            Ok t2 -> if t1 == t2 then Ok t1
                                                    else fail
                            Bad s -> Bad s
                        Bad s -> Bad s
infer env ELt    e1 e2 = infer env (ELt   e1 e2) -- should probably be some check here that e1 and e2 are comparable
infer env EGt    e1 e2 = infer env (EGt   e1 e2)
infer env ELtEq  e1 e2 = infer env (ELtEq e1 e2)
infer env EGtEq  e1 e2 = infer env (EGtEq e1 e2)
infer env EEq    e1 e2 = infer env (EEq   e1 e2)
infer env ENEq   e1 e2 = infer env (ENEq  e1 e2)
infer env EAnd   e1 e2 = infer env (EAnd  e1 e2)
infer env EOr    e1 e2 = infer env (EOr   e1 e2)
infer env EAss   id e1 = case snd(lookup(id)) of -- Not sure, perhaps just return the type of the righthand expr but check that that is the expression of the left hand
                        Ok e -> check env e
                        Bad s -> Bad s

lookupVar :: Env -> Id -> Err Type

lookupFun :: Env -> Id -> Err ([Type], Type)

updateVar :: Env -> Id -> Type -> Err Env

updateFun :: Env -> Id -> ([Type], Type) -> Err Env
updateFun (Env sig) id (argTypes, reType) = Map.update sig

newBlock  :: Env -> Env

emptyEnv  :: Env
emptyEnv = Env (Sig Map.empty) (Contex Map.empty)