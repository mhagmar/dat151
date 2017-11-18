module Env where

import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs

type Env = (Sig, [Context])
type Sig = Map Id ([Type], Type)
type Contex = Map Id Type