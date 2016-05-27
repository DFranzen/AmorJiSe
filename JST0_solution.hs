module JST0_solution where

import JST0_types
import Data.Map as Map

import JST0_constrain
import Debugging

--restructured
----------------------------
-- represents a solution for type variables 
-- i.e. a map from type variables to types
--
-- note:
-- - each type variable has its unique index, eventhough in JST0 some of them are associated with a string or with function parts.
-- - a type in the solution has to type variables anymore.
----------------------------
type Solution = Map Int Type

-- return an empty solution
solution_empty :: Solution
solution_empty = Map.empty 

-- return the type of a type variable
-- or None if the solution for this index in not known
solution_get :: Solution -> Int -> Type
solution_get s a = map_get_sol a s

--map_get_sol i s: get the type for TV index i from the solution s without the Just or Nothing bit
map_get_sol :: Int -> Solution -> Type
map_get_sol n s = let t = Map.lookup n s
                  in case t of
                    Just t1 -> t1
                    Nothing -> JST0_None

--solution_set s i t: insert the type t for the type index i into the soltution s
-- return new solution with this new type inserted.
solution_set :: Solution -> Int -> Type -> Solution
solution_set s i t = Map.insert i t s

solution_add_upperbound :: Solution -> Int -> Type -> Solution
solution_add_upperbound s i t = let
  old = map_get_sol i s
  in solution_set s i (min_type old t)
                                    
show_solution :: Solution -> String
show_solution s = Map.foldWithKey (\i t prv -> prv ++ (show i)) "" s
  --Map.foldWithKey (\i t prv -> prv ++ show_solution_one i t) "" s

show_solution_one :: Int -> Type -> String
show_solution_one i t = (show i) ++ " -- " ++ (show t) ++ "\n"

----------------------------------------
-- checks a solution against the set of constraints
----------------------------------------

check_solution :: Solution -> [Constrain] -> Bool
check_solution sol cs = Prelude.all (check_solution_one sol) cs

check_solution_one :: Solution -> Constrain -> Bool
check_solution_one sol c | trace 30 ("checking constrain " ++ (show c) ) False = undefined
check_solution_one sol c = let
  cp = constrain_eliminate_TVs sol c
  in check_constrain_single cp

constrain_eliminate_TVs :: Solution -> Constrain -> Constrain
constrain_eliminate_TVs sol (SubType t1 t2) = SubType (type_eliminate_TVs sol t1) (type_eliminate_TVs sol t2)
constrain_eliminate_TVs sol (Cast t1 t2) = SubType (type_eliminate_TVs sol t1) (type_eliminate_TVs sol t2)
constrain_eliminate_TVs sol (MemberExtend t1 m t2) = MemberExtend (type_eliminate_TVs sol t1) m (type_eliminate_TVs sol t2)
constrain_eliminate_TVs sol (Extend t1 t2) = Extend (type_eliminate_TVs sol t1) (type_eliminate_TVs sol t2)
constrain_eliminate_TVs sol (IsObject t) = IsObject (type_eliminate_TVs sol t)
constrain_eliminate_TVs sol (Only t ss) = Only (type_eliminate_TVs sol t) ss
constrain_eliminate_TVs sol (Only_type t1 t2) = Only_type (type_eliminate_TVs sol t1) (type_eliminate_TVs sol t2)
constrain_eliminate_TVs sol (Empty t) = Empty (type_eliminate_TVs sol t)

type_eliminate_TVs :: Solution -> Type -> Type
type_eliminate_TVs sol (JST0_TV a _ann) = solution_get sol a
type_eliminate_TVs sol (JST0_Function o t tp) = (JST0_Function (type_eliminate_TVs sol o) (types_eliminate_TVs sol t) (type_eliminate_TVs sol tp))
type_eliminate_TVs sol (JST0_Object alpha mem) = JST0_Object alpha (mems_eliminate_TVs sol mem)
type_eliminate_TVs sol (JST0_Ret t) = JST0_Ret (type_eliminate_TVs sol t)
type_eliminate_TVs _sol t = t

types_eliminate_TVs :: Solution -> [Type] -> [Type]
types_eliminate_TVs sol ts = Prelude.map (type_eliminate_TVs sol) ts

mems_eliminate_TVs :: Solution -> Members -> Members
mems_eliminate_TVs sol mem = Map.map (\(t,tf) -> (type_eliminate_TVs sol t,tf)) mem
