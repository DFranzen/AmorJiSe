module JST0P_solution where

import Data.Map as Map

import JST0P_types
import JST0_types
import JST0_type_aux
import JST0_solution

import Debugging

--import Debug.Trace

----------------------------------
-- represents a solution for type variables in JST0P
-- i.. a map from type variables to types
-- 
-- -note: a type in a solution has not type variables anymore
----------------------------------
type SolutionAn = (Map Int TypeAn)

-- return an empty solution
solutionAn_empty :: SolutionAn
solutionAn_empty = Map.empty

-- replace all TV in the given type by their solution
solutionAn_get :: SolutionAn -> Int -> TypeAn
solutionAn_get s a | trace 30 ("Looking up solution for " ++ show a ++ " in " ++ show s) False = undefined
solutionAn_get s a = case Map.lookup a s of
  Just t1 -> t1
  Nothing -> (JST0P_None,I 0,I 0)

solutionAn_set :: SolutionAn -> Int -> TypeAn -> SolutionAn
solutionAn_set s a t = Map.insert a t s

-- generate a solution in JST0P from a solution in JST0
solutionAn_from_solution :: Solution -> (SolutionAn,Int)
solutionAn_from_solution s = Map.foldrWithKey (\i t (prv,b) -> let (tp,bp) = (inflateAn t b) in (solutionAn_set prv i tp,bp)) (solutionAn_empty,0) s
--solutionP_from_solution s = solutionP_from_solutionlist s (Map.keys s)

-- Add annotations to a JST0 solution for all variables with indices in the given list. Returns the JST0P solution and the next usable index.
solutionAn_from_solutionlist :: Solution -> [Int] -> (SolutionAn,Int)
solutionAn_from_solutionlist _ [] = (solutionAn_empty,0)
solutionAn_from_solutionlist s (x:xs) = let
  (solAn,b) = solutionAn_from_solutionlist s xs
  (t,b1) = (inflateAn (solution_get s x) b)
  in ((solutionAn_set solAn x t),b1)

show_solutionAn :: SolutionAn -> String
show_solutionAn s = Map.foldWithKey (\i t prv -> prv ++ show_solutionAn_one i t) "" s

show_solutionAn_one :: Int -> TypeAn -> String
show_solutionAn_one i t = "    " ++ (show i) ++ " -- " ++ (show t) ++ "\n"

--
