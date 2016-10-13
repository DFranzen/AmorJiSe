module JST0_constrain where

import JST0_types
--import JST0_type_aux

import Data.Map as Map
import Data.Set as Set
--import Data.List as List

import Debugging

data Constrain = SubType Type Type
               | Cast Type Type
               | MemberExtend Type String Type
               | Extend Type Type
               | IsObject Type
               | Only Type [String] -- Type has not more than the following definite members
               | Only_type Type Type -- Type has not more definite members than the other                 
               | Empty Type
               deriving Eq
                 
instance Show Constrain where
  show (SubType t1 t2) = (show t1) ++ "≤" ++ (show t2)
  show (Cast t1 t2) = (show t1) ++ "≤_c" ++ (show t2) 
  show (IsObject t) = "(" ++ (show t) ++ ")^{obj}"
  show (MemberExtend t1 m t2) = (show t1) ++ "⊲_" ++ (show m) ++ (show t2)
  show (Extend t1 t2) = (show t1) ++ "⊲_*" ++ (show t2)
  show (Empty t1) = (show t1) ++ "°"
  show (Only t1 s) = (show t1) ++ "≤_⚫" ++ (show s)
  show (Only_type t1 t2) = (show t1) ++ "≤_⚫" ++ (show t2)

instance Ord Constrain where
  compare a b = compare (show a) (show b)

----------------------------------------
-- check a set of constraints with no TVs
----------------------------------------

check_constrain_all :: [Constrain] -> Bool
check_constrain_all cs = Prelude.all check_constrain_single cs

check_constrain_single :: Constrain -> Bool
check_constrain_single c | trace 30 ("check_constrain_single " ++ show c) False = undefined
check_constrain_single (Empty t) | check_constrain_empty t = True
                                 | error "!! Emtpy type is required to have Definire MEmber" True = undefined
check_constrain_single (Only t defs) | object_contain_at_most t defs  = True
                                     | error "\n!!! Absent Member needs to be Definite" True = undefined
check_constrain_single (Only_type t t2) | trace 30 ("Check: " ++ show (Only_type t t2)) False = undefined
                                        | t == t2 = True
                                        | object_contain_at_most t (object_get_Definites t2) = True
                                        | error ("\n!!! Potential Member needs to be Definite in " ++ show t) True = undefined
check_constrain_single _ = True



----------------------------------------
-- check all the constraints for a particular solution for a type variable
----------------------------------------

check_constraints :: [Constrain] -> Type -> Bool
check_constraints cs t = Prelude.foldr (\a b -> (check_constrain a t) && b) True cs

check_constrain :: Constrain -> Type -> Bool
check_constrain (Empty _) t = check_constrain_single (Empty t)
check_constrain (Only _ defs) t = check_constrain_single (Only t defs)
check_constrain (Only_type _ t2) t = check_constrain_single (Only_type t t2)
check_constrain _ _ = True

----------------------------------------
-- single checking methods for constraints
----------------------------------------

check_constrain_empty :: Type -> Bool
check_constrain_empty t | object_contain_at_most t [] = True
                        | error ("Type " ++ show t ++ " should be empty") = undefined
                        | otherwise = False

--check_constrain_only :: Members -> [String] -> Bool
--check_constrain_only mems defs =
--  Map.foldWithKey (\s (_,psi) b -> (b && ((psi == Potential) || (List.elem s defs)))) True mems
--check_constrain_only _ _ = True


should_be_empty :: [Constrain] -> Bool
should_be_empty [] = False
should_be_empty ((Empty _):_) = True
should_be_empty (_:cs) = should_be_empty cs

cs_show_varinfo :: [Constrain] -> String
cs_show_varinfo cs = let tvs = JST0_constrain.get_TVs_list cs
                     in Map.foldWithKey (\i s prv -> (prv ++ "\n" ++ show i ++ ":" ++ s)) "" tvs

-- return a list of all types in a constraint
get_types :: Constrain -> [Type]
get_types (SubType t1 t2) = [t1,t2]
get_types (Cast t1 t2) = [t1,t2]
get_types (IsObject t) = [t]
get_types (Empty t) = [t]
get_types (MemberExtend t1 _ t2) = [t1,t2]
get_types (Extend t1 t2) = [t1,t2]
get_types (Only t _) = [t]
get_types (Only_type t1 t2) = [t1,t2]

-- return a map of the used type variables
get_TVs :: Constrain -> Map Int String
get_TVs c = JST0_types.get_TVs_list (get_types c)

get_TVs_list :: [Constrain] -> Map Int String
get_TVs_list cs = Map.unions (Prelude.map JST0_constrain.get_TVs cs)

-- return a set of all variables used in a constraint
get_TVs_index :: Constrain -> Set Int
get_TVs_index c = JST0_types.get_TVs_index_list (get_types c)

get_TVs_index_list :: [Constrain] -> Set Int
get_TVs_index_list cs = Set.unions (Prelude.map JST0_constrain.get_TVs_index cs)

get_first_TV_index :: Constrain -> Int
get_first_TV_index c | trace 30 ("get_first_TV_index " ++ (show c)) False = undefined
get_first_TV_index c = let
  ts = JST0_constrain.get_TVs_index c
  in Set.findMin ts

-- compute the type of a sequence of two expressions which have the following type.
-- Usually the second type will be chosen, except for when the first expression was a return expression
-- Argument:
--   - Type of the first expression in the sequence
--   - Type of the 2nd expression in the sequence
--   - Index of the next TV to be chosen
-- Returns:
--   - Type of the whole sequence
--   - Index of next TV to be chosen
--   - List of constrain generated
seq_type :: Int -> Type -> Type -> (Int,Type,[Constrain])
seq_type a t1 t2 | trace 10 "seq_type" False = undefined
seq_type a (JST0_Ret t1) (JST0_Ret t2) = let
  t = JST0_TV a "Sequence"
  in (a+1,JST0_Ret t,[SubType t1 t,SubType t2 t])
seq_type a (JST0_Ret t) _t2 | error "Return on some paths only" = (a,JST0_Ret t,[])
seq_type a _t1 t2 = (a,t2,[])

-- return all Constraints neccessary to make two lists component-wise subtypes
makeSubtype_list :: [Type] -> [Type] -> [Constrain]
makeSubtype_list = Prelude.zipWith (\a b -> (SubType a b)) 

-- return true if the two constraints have no type variables in common
disjunct :: Constrain -> Constrain -> Bool
disjunct a b = let
  ai = JST0_constrain.get_TVs_index a
  bi = JST0_constrain.get_TVs_index b
  is = Set.intersection ai bi
  in (Set.size is) == 0

const :: Constrain -> Bool
const c = let
  ts = get_types c
  in Prelude.foldr (\t prv -> (JST0_types.const t) && prv) True ts

-- return true if one of the high level types are TV
tv_rel :: Constrain -> Bool
tv_rel c = let
  ts = get_types c
  in Prelude.foldr (\t prv -> (is_TV t) || prv) False ts

tv_rel_get :: Constrain -> Int
tv_rel_get c = let
  ts = get_types c
  in get_first_TVindex ts

tv_rel_get_all :: Constrain -> Set Int
tv_rel_get_all c = let
  ts = get_types c
  in get_all_TVindex ts
