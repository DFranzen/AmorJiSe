module JST0P_context
       (
         ContextAn,
         JST0P_context.empty,
         empty_empty,
         JST0P_context.var_get,
         var_get_definite,
         var_set,
         var_set_list,
         var_set_path_list,
         var_create_path_list,
         var_names,
         get_vars,
         sol_set,
         context_min_constrain,
        -- context_sub_constrain,
         aug_context,
         deg_context,
         contextAn_toNiceString
       ) where

---------------------------------
-- a environment describes Gamma and P of the typing rules
-- both are modeled as List of names and types.
-- The JST0P environment has furthermore a solution for the type variables with it from the JST0 type inference#
-- The environment caries Annotations for every variable, because in JavaScript each object can become a scope object and vice versa
---------------------------------

import Data.Map as Map
import Data.Set as Set

import JST0_types
import JST0_type_aux
import JST0P_types
import JST0P_constrain
import JST0_context (Context,var_get)
import JST0P_solution

import Debugging

type ContextAn = (MembersAn,SolutionAn)

empty :: SolutionAn -> ContextAn
empty sol = (Map.empty,sol)

empty_empty :: ContextAn
empty_empty = (Map.empty,solutionAn_empty)

empty_c :: ContextAn -> ContextAn
empty_c (_g,sol) = (Map.empty,sol)

var_lookup :: ContextAn -> String -> Maybe (TypeAn,FieldType)
var_lookup (g,_sol) s = Map.lookup s g

var_set :: ContextAn -> String -> (TypeAn,FieldType) -> ContextAn
var_set (g,sol) s t = (Map.insert s t g,sol)

sol_lookup :: ContextAn -> Int -> TypeAn
sol_lookup (_g,sol) t = solutionAn_get sol t

var_get :: ContextAn -> String -> (TypeAn,FieldType)
var_get (g,sol) s = case (var_lookup (g,sol) s) of
  Just (t,psi) -> (t,psi)
  Nothing -> let x| trace 1 ("Variable not declared: " ++ s) False = undefined
             in ((JST0P_None,I 0,I 0),Potential)

var_get_definite :: ContextAn -> String -> TypeAn
var_get_definite c s = 
  let 
    (t_pre,psi) = JST0P_context.var_get c s
    t | (psi == Definite) = t_pre
      | trace 1 ("Reading from uninitialized Variable " ++ s) False = undefined
  in t
                 
var_set_list :: ContextAn -> [String] -> [(TypeAn,FieldType)] -> ContextAn
var_set_list e [] [] = e
var_set_list e (s:ss) (t:ts) = var_set (var_set_list e ss ts) s t

var_set_path :: ContextAn -> Path -> (TypeAn,FieldType) -> ContextAn
var_set_path g [] _t = g
var_set_path g [var] t = var_set g var t
var_set_path g (o:ps) (t,_psit) = let
  to = var_lookup g o
  tonew = case to of
    Just (tor,_psitor) -> objectAn_set_path tor ps (t,Definite)
--    Nothing -> objectAn_set_path (JST0P_None,I 0) ps (t,Definite)
  in var_set g o (tonew,Definite)

var_set_path_list :: ContextAn -> [Path] -> [(TypeAn,FieldType)] -> ContextAn
var_set_path_list c [] [] = c
var_set_path_list c (p:ps) (t:ts) = let
  c2 = var_set_path c p t
  in var_set_path_list c2 ps ts

var_create_path :: ContextAn -> Path -> (TypeAn,FieldType) -> ContextAn
var_create_path g [] _t = g
var_create_path g [var] t = var_set g var t
var_create_path g (o:ps) (t,_psit) = let
  to = var_lookup g o
  tonew = case to of
    Just (tor,_psitor) -> objectAn_set_path tor ps (t,Definite)
    Nothing -> objectAn_set_path (JST0P_None,I 0,I 0) ps (t,Definite)
  in var_set g o (tonew,Definite)

var_create_path_list :: ContextAn -> [Path] -> [(TypeAn,FieldType)] -> ContextAn
var_create_path_list c [] [] = c
var_create_path_list c (p:ps) (t:ts) = let
  c2 = var_create_path c p t
  in var_create_path_list c2 ps ts



var_contains :: ContextAn -> String -> Bool
var_contains (g,sol) s = Map.member s g

var_names :: ContextAn -> [String]
var_names (g,_sol) = Map.keys g

var_names_set :: ContextAn -> Set String
var_names_set (g,_sol) = Map.keysSet g

sol_set :: ContextAn -> SolutionAn -> ContextAn
sol_set (c,_sol) sol = (c,sol)

context_min_constrain :: ContextAn -> ContextAn -> (Int,Int) -> ([ConstrainAn],ContextAn,Int,Int)
context_min_constrain g1 g2 (a,b) | trace 30 ("context_min_constrain: " ++ show (a,b) ++ "," ++ show (var_names g1) ++ "," ++ show (var_names g2)) False = undefined
context_min_constrain g1 g2 (a,b) = vars_min_constrain g1 g2 (a,b) (get_union_set g1 g2)

vars_min_constrain :: ContextAn -> ContextAn -> (Int,Int) -> [String] -> ([ConstrainAn],ContextAn,Int,Int)
vars_min_constrain _g1 _g2 (a,_b) ss | trace 35 ("vars_min_constrain: " ++ show a ++ ", " ++ show ss) False = undefined
vars_min_constrain g1 _g2 (a,b) [] = ([],empty_c g1,a,b)
vars_min_constrain g1 g2 (a,b) (s:ss) = let
  (c_ss,g,a_ss,b_ss) = vars_min_constrain g1 g2 (a,b) ss
  (c_s,t,a_s,b_s) = var_min_constrain g1 g2 (a_ss,b_ss) s
  in (concat [c_ss,c_s],JST0P_context.var_set g s t,a_s,b_s)

----------------------------------------
-- compute a type which is smaller than the two types of the variable s in the two given contexts.
----------------------------------------
-- inputs: 
--   - contexts to be bigger than the result
--   - New indices for type variable and annotation variable
--   - variable name to be minimized
-- output:
--   - List of constraints needed to make this work
--   - New type of the variable in the merged context
--   - new state of the variable in the merged context
--   - new indices for type variable and annotation variable
----------------------------------------
var_min_constrain :: ContextAn -> ContextAn -> (Int,Int) -> String -> ([ConstrainAn],(TypeAn,FieldType),Int,Int)
var_min_constrain g1 g2 (a,_b) s | trace 30 ("var_min_constrain: " ++ ", " ++ show s ++ ":" ++ show (var_lookup g1 s,var_lookup g2 s)) False = undefined
var_min_constrain g1 g2 (a,b) s = let
  (t1,psi1) = case var_lookup g1 s of
    Just tp -> tp
--    Nothing -> ((JST0P_None,I 0),Potential)
  (t2,psi2) = case var_lookup g2 s of
    Just tp -> tp
--    Nothing -> ((JST0P_None,I 0),Potential)
  (t,c_t) | is_none t1 = (t2,[])
          | is_none t2 = (t1,[])
          | otherwise = let
    tt = sol_lookup g1 a
    in  (tt,makeMin t1 t2 tt)
  in (c_t,(t,min_field_type psi1 psi2),a+1,b+2)

--context_sub_constrain :: ContextAn -> ContextAn -> [ConstrainAn]
--context_sub_constrain (g1,_sol1) (g2,_sol2) = Set.toList (makeGreater g1 g2
    
     
get_union_set :: ContextAn -> ContextAn -> [String]
get_union_set g1 g2 = Set.elems (Set.union (var_names_set g1) (var_names_set g2))


aug_context :: Context -> Int -> SolutionAn -> (ContextAn,Int)
aug_context m b sol = aug_context_those m b sol (Map.keys m)

aug_context_those :: Context -> Int -> SolutionAn -> [String] -> (ContextAn,Int)
aug_context_those _m b sol [] = (JST0P_context.empty sol,b)
aug_context_those m b sol (s:ss) = let
  (t,psi) = JST0_context.var_get m s
  (tp,b2) = case t of
    (JST0_TV a _ann) -> (solutionAn_get sol a,b)
    _ -> inflateAn t b
  (rest,bp) = aug_context_those m b2 sol ss
  in (var_set rest s (tp,psi),bp+1)

deg_context :: ContextAn -> Context
deg_context (con,_sol) = Map.map (\(t,tf) -> (deflateAn t,tf)) con


----------------------------------------
-- Return all annotation variables used within this context
----------------------------------------

get_vars :: ContextAn -> [Int]
get_vars (mem,_sol) = membersAn_get_vars mem


contextAn_toNiceString :: ContextAn -> String
contextAn_toNiceString (m,sol) = (Map.foldWithKey (\s ty prv -> prv ++ (contextAn_toNiceString_one s ty)) "" m)

contextAn_toNiceString_one :: String -> (TypeAn,FieldType) -> String
contextAn_toNiceString_one s (t,tf) = "    " ++ (show s) ++ ":" ++ (show t) ++ (show tf) ++ "\n"
