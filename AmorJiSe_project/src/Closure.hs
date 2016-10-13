module Closure (
  close_constraints,
  extract_solution,
  extract_HL_types
  ) where

-- import Data.Map
import Data.Map as Map
import Data.Set as Set

import Maps

import JST0_constrain
import JST0_types
import JST0_type_aux
import JST0_solution

import Debugging

-- API method to close a set of constraints
close_constraints :: [Constrain] -> Int -> Int -> CMap
close_constraints (x:xs) d _r | trace 25 ("close_constraints " ++ show d ++ ": " ++ show x) False = undefined
close_constraints [] _d _r= cmap_empty
close_constraints (x:xs) d r = let
  cs = close_constraints xs (d+1) (r-1)
  res | trace 25 ("Inserted:  " ++ show d ++ " Remaining: " ++ show r) True = insert_and_close cs x
      | otherwise = undefined
  in res

-- insert a new constrain into the CMAP and (if neccessary insert all constraints in the closure)
insert_and_close :: CMap -> Constrain -> CMap
--insert_and_close cmap c | trace 25 ("Inserting " ++ show c ++ " into " ++ show cmap) False = undefined
insert_and_close cmap c | trace 25 ("Inserting " ++ show c) True = let
  -- insert new constraint
  (cmap1,b2) = cmap_check_and_insert cmap c
  b | trace 30 ("Check came back " ++ show b2) True = b2
    | otherwise = undefined
  in case b of
    -- not a new constraint
    True -> cmap
    -- New constraint -> close it with all the relevant others
    False -> let
      -- close on its own
      cmap2 | is_closeCongFunc c = cc_closeCongFunc cmap1 c
            | otherwise = cmap1
      cmap3 | is_equi c = cc_closeEqui cmap2 c
            | otherwise = cmap2
      -- get all the relevant TVs
      ind = Set.insert (-1) (JST0_constrain.get_TVs_index c)
      -- get all the relevant constraints
      cs = Set.map (\i -> (cmap_geti cmap3 i)) ind
      in close_WithSetCSet cmap3 c cs

insert_and_close_list :: CMap -> [Constrain] -> CMap
insert_and_close_list cmap xs | trace 30 "insert_and_close_list" False = undefined
insert_and_close_list cmap [] = cmap
insert_and_close_list cmap (x:xs) = let
  i1 = insert_and_close cmap x
  in insert_and_close_list i1 xs

-- close one given constraint with a Set of Constraints and insert the resulting new constraints into the given CMap
--close_WithConstraintSet :: CMap -> Constrain -> Set Constrain -> CMap
--close_WithConstraintSet

-- close one given constraint with a Constraint and insert the resulting new Constrains into the given CMap
close_WithConstraint :: CMap -> Constrain -> Constrain -> CMap
close_WithConstraint _cm c cp | trace 25 ("Close WithConstrain " ++ show c ++ " with " ++ show cp) False = undefined
close_WithConstraint cm c cp = close_apply_list cm [
  (is_closeEmpty,       cc_closeEmpty      ),
  (is_closeObj,         cc_closeObj        ), 
  (is_closeTrans,       cc_closeTrans      ),
  (is_closeTransMem,    cc_closeTransMem   ),
  (is_closeBalance,     cc_closeBalance    ),
  (is_closeBalanceMem,  cc_closeBalanceMem ),
  (is_closeBalanceMems, cc_closeBalanceMems),
  (is_closeCong,        cc_closeCong       )] c cp

close_apply_list :: CMap -> [(Constrain -> Constrain -> Bool,CMap -> Constrain -> Constrain -> CMap)] -> Constrain -> Constrain -> CMap
close_apply_list cm l c1 c2 | trace 30 "close_apply_list" False = undefined
close_apply_list cm l c1 c2 = Prelude.foldr (\(is,cc) prv -> close_apply prv is cc c1 c2) cm l
     
close_apply:: CMap -> (Constrain -> Constrain -> Bool) -> (CMap -> Constrain -> Constrain -> CMap) -> Constrain -> Constrain -> CMap
close_apply cm is cc c1 c2 = let
  -- one way
  cm1 = if (is c1 c2) then cc cm  c1 c2 else cm
  -- reverse way
  cm2 = if (is c2 c1) then cc cm1 c2 c1 else cm1
  in cm2

-- close one given constraint with a set of constraints
close_WithCSet :: CMap -> Constrain -> CSet -> CMap
close_WithCSet _cm c cs | trace 30 ("Close WithCSet " ++ show c ++ " with " ++ show cs) False = undefined
close_WithCSet cm c cs = Map.fold (\cp prv -> close_WithConstraint prv c cp) cm cs

close_WithSetCSet :: CMap -> Constrain -> Set CSet -> CMap
close_WithSetCSet _cm c css | trace 30 ("Close WithSetCSet " ++ show c ++ " with " ++ show css) False = undefined
close_WithSetCSet cm c css = Set.fold (\cp prv -> close_WithCSet prv c cp) cm css

is_equi :: Constrain -> Bool
is_equi (SubType t1 t2) = is_Simple t1 || is_Simple t2 || is_Function t1 || is_Function t2
is_equi _ = False

is_closeEmpty :: Constrain -> Constrain -> Bool
is_closeEmpty (SubType t1 _t1p) (Empty t) = (t /= JST0_None) && (t1 == t)
is_closeEmpty _ _ = False

is_closeObj :: Constrain -> Constrain -> Bool
is_closeObj (SubType t1 t1p) (IsObject t2) = (t2 /= JST0_None) && ((t1 == t2) || (t1p == t2))
is_closeObj _ _ = False

is_closeTrans :: Constrain -> Constrain -> Bool
is_closeTrans (SubType _t1 t1p) (SubType t2 _t2p) = (t1p == t2) && (t2 /= JST0_None)
is_closeTrans (Cast    _t1 t1p) (Cast    t2 _t2p) = (t1p == t2) && (t2 /= JST0_None)
is_closeTrans (SubType _t1 t1p) (Cast    t2 _t2p) = (t1p == t2) && (t2 /= JST0_None)
is_closeTrans (Cast    _t1 t1p) (SubType t2 _t2p) = (t1p == t2) && (t2 /= JST0_None)
is_closeTrans _ _ = False

is_closeTransMem :: Constrain -> Constrain -> Bool
is_closeTransMem (MemberExtend _t1 _m1 t1p) (SubType t2 _to) =
  (t1p == t2) && (t2 /= JST0_None)
is_closeTransMem (Extend _t1 t1p) (SubType t2 _to) =
  (t1p == t2) && (t2 /= JST0_None)
is_closeTransMem _ _ = False

is_closeBalance :: Constrain -> Constrain -> Bool
is_closeBalance (SubType t1 _t1p) (SubType t2 t2p) =
  (t1==t2) && (t1/=JST0_None) &&
  ((is_Function t2p) || (is_Simple t2p))
is_closeBalance (SubType t1 _t1p) (Cast    t2 t2p) =
  (t1==t2) && (t1/=JST0_None) &&
  (is_Simple t2p)
is_closeBalance (Cast    t1 _t1p) (SubType t2 t2p) =
  (t1==t2) && (t1/=JST0_None) &&
  (is_Simple t2p)
is_closeBalance _ _= False

is_closeBalanceMem :: Constrain -> Constrain -> Bool
is_closeBalanceMem (MemberExtend t1 _m1 _t1p) (SubType t2 _to) =
  (t1 == t2) && (t2 /= JST0_None)
is_closeBalanceMem _ _ = False

is_closeBalanceMems :: Constrain -> Constrain -> Bool
is_closeBalanceMems (Extend t1 _t1p) (SubType t2 _to) =
  (t1 == t2) && (t2 /= JST0_None)
is_closeBalanceMems _ _ = False


is_closeCong :: Constrain -> Constrain -> Bool
is_closeCong (SubType t1 t1p) (SubType t2 t2p) =
  (t1 == t2) && (t1/=JST0_None) &&
  (is_Object t1p) &&
  (is_Object t2p)
is_closeCong _ _ = False

is_closeCongFunc :: Constrain ->  Bool
is_closeCongFunc (SubType t1 t1p) = (is_Function t1) && (is_Function t1p)
is_closeCongFunc _ = False

cc_closeEmpty :: CMap -> Constrain -> Constrain -> CMap
cc_closeEmpty _cm c1 c2 | trace 11 ("closeEmpty " ++ show c1 ++ "," ++ show c2) False = undefined
cc_closeEmpty cm (SubType _t1 t1p) (Empty _t) = insert_and_close cm (Empty t1p)
cc_closeEmpty _cm _c1 _c2 = undefined

cc_closeObj :: CMap -> Constrain -> Constrain -> CMap
cc_closeObj _cm c1 c2 | trace 11 ("closeObj " ++ show c1 ++ "," ++ show c2) False = undefined
cc_closeObj cm (SubType t1 t1p) (IsObject _t) = insert_and_close (insert_and_close cm (Empty t1)) (Empty t1p)
cc_closeObj _cm _c1 _c2 | error ("Trying to closeObj with non compatible constraints") = undefined
                        | otherwise = undefined

cc_closeTrans :: CMap -> Constrain -> Constrain -> CMap
cc_closeTrans _cm c1 c2 | trace 11 ("closeTrans " ++ show c1 ++ "," ++ show c2) False = undefined
cc_closeTrans cm (SubType t1 _t1p) (SubType _t2 t2p) =
  insert_and_close cm (SubType t1 t2p)
cc_closeTrans cm (Cast    t1 _t1p) (Cast    _t2 t2p) =
  insert_and_close cm (Cast t1 t2p)
cc_closeTrans cm (SubType t1 _t1p) (Cast    _t2 t2p) =
  insert_and_close cm (Cast t1 t2p)
cc_closeTrans cm (Cast    t1 _t1p) (SubType _t2 t2p) =
  insert_and_close cm (Cast t1 t2p)
cc_closeTrans _cm _c1 _c2 = undefined

cc_closeTransMem :: CMap -> Constrain -> Constrain -> CMap
cc_closeTransMem _cm c1 c2 | trace 11 ("closeTransMem " ++ show c1 ++ "," ++ show c2) False = undefined
cc_closeTransMem cm (MemberExtend t1 _m _t1p) (SubType _t2 to) | is_Object to =let 
  new_l = members_closeTransMem t1 to (object_get_fieldnames to)
  in insert_and_close_list cm new_l
                                                               | otherwise =
  insert_and_close cm (SubType t1 to)
cc_closeTransMem cm (Extend t1 _t1p) (SubType _t2 to) | is_Object to = let
  new_l = members_closeTransMem t1 to (object_get_fieldnames to)
  in insert_and_close_list cm new_l
                                                      |otherwise =
  insert_and_close cm (SubType t1 to)
cc_closeTransMem _cm _c1 _c2 = undefined

cc_closeBalance :: CMap -> Constrain -> Constrain -> CMap
cc_closeBalance _cm c1 c2 | trace 11 ("closeBalanceMem " ++ show c1 ++ "," ++ show c2) False = undefined
cc_closeBalance cm (SubType _t1 t1p) (SubType _t2 t2p) =
  let new = (SubType t1p t2p)
  in insert_and_close cm new
cc_closeBalance cm (Cast    _t1 t1p) (SubType _t2 t2p) =
  let new = (Cast t2p t1p)
  in insert_and_close cm new
cc_closeBalance cm (SubType _t1 t1p) (Cast    _t2 t2p) =
  let new = (Cast t1p t2p)
  in insert_and_close cm new
cc_closeBalance _cm _c1 _c2 = undefined

cc_closeBalanceMem :: CMap -> Constrain -> Constrain -> CMap
cc_closeBalanceMem _cm c1 c2 | trace 11 ("closeBalanceMem " ++ show c1 ++ "," ++ show c2) False = undefined
cc_closeBalanceMem cm (MemberExtend _t1 m1 t1p) (SubType _t2 to) =
  let new_l = members_closeBalanceMem t1p to m1 (object_get_fieldnames to)
  in insert_and_close_list cm new_l
cc_closeBalanceMem _cm _c1 _c2 = undefined

cc_closeBalanceMems :: CMap -> Constrain -> Constrain -> CMap
cc_closeBalanceMems _cm c1 c2 | trace 11 ("closeBalanceMems " ++ show c1 ++ "," ++ show c2) False = undefined
cc_closeBalanceMems cm (Extend t1 t1p) (SubType _t2 to) | is_Object to = let 
  new_l = members_closeBalanceMems t1p to (object_get_fieldnames to)
  in insert_and_close_list cm new_l
                                                         | otherwise =
  insert_and_close cm (SubType t1 t1p)
cc_closeBalanceMems _cm _c1 _c2 = undefined

cc_closeCong :: CMap -> Constrain -> Constrain -> CMap
cc_closeCong _cm c1 c2 | trace 11 ("closeCong " ++ show c1 ++ "," ++ show c2) False = undefined
cc_closeCong cm (SubType _t1 t1p) (SubType _t2 t2p) = let
  -- TODO: unrolling?
  new_l = members_closeCong t1p t2p (concat [object_get_fieldnames t1p,object_get_fieldnames t2p])
  in insert_and_close_list cm new_l
cc_closeCong _cm _c1 _c2 = undefined

cc_closeCongFunc :: CMap -> Constrain -> CMap
cc_closeCongFunc _cm c | trace 11 ("closeCongFunc " ++ show c) False = undefined
cc_closeCongFunc cm (SubType (JST0_Function o1 t1 t1p) (JST0_Function o2 t2 t2p)) =
  let new_l1 = close_list t1 t2
      new_l2 = close_list t2 t1
      cm1 = insert_and_close_list cm  new_l1
      cm2 = insert_and_close_list cm1 new_l2
      cm3 = insert_and_close cm2 (SubType t1p t2p)
      cm4 = insert_and_close cm3 (SubType t2p t1p)
      cm5 = insert_and_close cm4 (SubType o2 o1)
      cm6 = insert_and_close cm5 (SubType o1 o2)
  in cm6
cc_closeCongFunc _cm _c1 = undefined

cc_closeEqui :: CMap -> Constrain -> CMap
cc_closeEqui cm (SubType t1 t2) = insert_and_close cm (SubType t2 t1)
cc_closeEqui _cm _c = undefined

close_list :: [Type] -> [Type] -> [Constrain]
close_list [] _ = []
close_list _ [] = []
close_list a b = close_listp a b

close_listp :: [Type] -> [Type] -> [Constrain]
close_listp [] [] = []
close_listp (x:xs) (y:ys) = (SubType x y):(close_list xs ys)
close_listp _ _ = undefined

--members_closeBalanceMems: compute all the Constraints SubType t<[m:(tpp,Potential)] for m given in the list
members_closeBalanceMems :: Type -> Type -> [String] -> [Constrain]
members_closeBalanceMems _ _ [] = []
members_closeBalanceMems t to (m:ms) = let
  (a,tpp,_) = object_get_singleton_parts to m
  psip | trace 30 ("CloseBalanceMems " ++ show (SubType t (object_singleton a m tpp Potential))) True = Potential
  in (SubType t (object_singleton a m tpp psip)):(members_closeBalanceMems t to ms)

--members_closeTransMem: compute all the Constraints SubType t<[m:to(m)] for m given in the list
members_closeTransMem :: Type -> Type -> [String] -> [Constrain]
members_closeTransMem _ _ [] = []
members_closeTransMem t to (m:ms) = let
  (a,tpp,psi) = object_get_singleton_parts to m
  in (SubType t (object_singleton a m tpp psi)):(members_closeTransMem t to ms)

--members_closeBalanceMem: compute all the constraints t<[m:to(m)] where psi(mp)=Potential
members_closeBalanceMem :: Type -> Type -> String -> [String] -> [Constrain]
members_closeBalanceMem _ _ _ [] = []
members_closeBalanceMem t to mp (m:ms) = let
  (a,tpp,psi) = object_get_singleton_parts to m
  psip = if (m==mp)
         then Potential
         else psi
  in (SubType t (object_singleton a m tpp psip)):(members_closeBalanceMem t to mp ms)

--members_closeCong: compute all possible constraints tp<tpp in the closeCong case
-- Arguments:
--  - Object type from first subtyping relation
--  - Object type from second subtyping relation
--  - String which to use as m
-- Return
--  Set of constraints comning out of this case
members_closeCong :: Type -> Type -> [String] -> [Constrain]
members_closeCong _ _ [] = []
members_closeCong to1 to2 (m:ms) = let
  tp = object_get_type to1 m
  tpp = object_get_type to2 m
  rest = members_closeCong to1 to2 ms
  in (SubType tp tpp):((SubType tpp tp):rest)
     
----------------------------------------
-- Extract HL types from the Constraint list
----------------------------------------

--extract the HL types of all TVs invoved
extract_HL_types :: CMap -> (HL_Map)
extract_HL_types cm = Map.mapWithKey (hltype_from_constraints) cm

hltype_from_constraints :: Int -> CSet -> HL_Type
hltype_from_constraints i cs = Map.fold (\c prv -> add_HL_types (hltype_from_constraint i c) prv) HL_None cs

-- extract the Higher level type for TV with the given index from the given constrain
hltype_from_constraint :: Int -> Constrain -> HL_Type
hltype_from_constraint i1 (Empty (JST0_TV i2 _ann)) | (i1 == i2) = HL_Object
hltype_from_constraint i1 (IsObject (JST0_TV i2 _ann)) | (i1 == i2) = HL_Object
hltype_from_constraint i1 (SubType (JST0_TV i2 _ann) t) | (i1 == i2) = get_HL_type t
hltype_from_constraint i1 (SubType t (JST0_TV i2 _ann)) | (i1 == i2) = get_HL_type t
hltype_from_constraint i1 (MemberExtend (JST0_TV i2 _ann) _m _t2) | (i1 == i2) = HL_Object
hltype_from_constraint i1 (MemberExtend _t2 _m (JST0_TV i2 _ann)) | (i1 == i2) = HL_Object
hltype_from_constraint i1 (Extend (JST0_TV i2 _ann) t) | (i1 == i2) = get_HL_type t
hltype_from_constraint i1 (Extend t (JST0_TV i2 _ann)) | (i1 == i2) = get_HL_type t
hltype_from_constraint i1 (Only (JST0_TV i2 _ann) _l) | (i1 == i2) = HL_Object
hltype_from_constraint i1 (Only_type (JST0_TV i2 _ann) t) | (i1 == i2) = get_HL_type t
hltype_from_constraint i1 (Only_type t (JST0_TV i2 _ann)) | (i1 == i2) = get_HL_type t
hltype_from_constraint i1 (Cast (JST0_TV i2 _ann) t) | (i1 == i2) = hl_to_at_least (get_HL_type t)
hltype_from_constraint _i _c = HL_None
----------------------------------------
-- Check that the Constraints are wellformed
----------------------------------------


-- check the wellformedness of the Constraints set and collect HL type information and sorted constraints on the way
-- Arguments: List of Constraints
-- Returns: Map from TV indices to Higher level type and set of Constraints for this TV
-- Will return matching error, if not well_formed
well_formed :: [Constrain] -> HL_Map -> Bool
well_formed [] _hlmap = True
well_formed (c:cs) hlmap = let
  rest = well_formed cs hlmap
  in rest && well_formed_one c hlmap

-- check one Constrain
-- Arguments: Constrain to handle and existing HL_Map
-- return: True if well formed
-- Will return matching error if not well_formed
well_formed_one :: Constrain -> HL_Map -> Bool
well_formed_one (Empty t) m = hl_map_consistent m t HL_Object
well_formed_one (Only t s) m = hl_map_consistent m t HL_Object
well_formed_one (Only_type t t2) m = hl_map_consistent m t HL_Object
well_formed_one (SubType t1 t2) m = hl_map_consistent_pair m t1 t2
well_formed_one (MemberExtend t1 s t2) m = hl_map_consistent_pair m t1 t2
well_formed_one (Extend t1 t2) m = hl_map_consistent_pair m t1 t2
well_formed_one (IsObject t) m = hl_map_consistent m t HL_Object

-------------------------------------------
-- Get the solution from the HL types
-------------------------------------------

--extracty the solution for all TVs from a bunch of closend constraints
-- Arguments:
--  - closed list of constraints
-- Returns: minimal Solution for all TVs
extract_solution :: CMap -> Solution
extract_solution cmap = let hl = extract_HL_types cmap
                            sol = extract_solution_all (Map.keys cmap) (hl,cmap)
                            -- _correct | check_solution cs sol = True
                        in sol

-- extract all solutions for the given TVs
-- Arguments:
--  - list of all indices for TVs to extract
--  - HigherLevel information about all the TVs
-- Returns solution for all TVs with indices in the first argument
extract_solution_all :: [Int] -> (HL_Map,CMap) -> Solution
extract_solution_all is (hl,cm) = Prelude.foldr (\i prv ->
                                                  (solution_set prv i
                                                   (extract_type Set.empty (hl,cm) i)
                                                  )
                                                )
                                  solution_empty
                                  is

-- Main auxiliary function.
-- Arguments:
--  - Set of already bound recursive indices
--  - The HL type information
--  - index of the TV to infer a type for
-- Returns: Solution for all 
extract_type :: (Set Int) -> (HL_Map,CMap) -> Int -> Type
extract_type s (m,cmap) i = if (Set.member i s)
                            then JST0_Alpha (Beta i)
                            else let (t,cs) = (hl_map_geti m i,cmap_geti cmap i)
                                 in case t of
                                   HL_simple tp -> tp
                                   HL_at_most tp -> tp
                                   HL_return -> extract_type_return s (m,cmap) i cs
                                   HL_None -> JST0_None
                                   HL_Function -> extract_type_function s (m,cmap) i cs
                                   HL_Object -> let
                                     sp = Set.insert i s --bind i
                                     inf = extract_type_object sp (m,cmap) i cs
                                     in inf

-- extract the type for a type from the HL_Map
-- what's the full solution for this type given these constraints
-- -> replace all type variables in this type by the appropriate solution
-- Arguments:
--   - Set of already bound Alpha indices
--   - High level type map & constraints map
--   - currently infered type
-- Return: TV less solution for the given type
extract_type_type :: (Set Int) -> (HL_Map,CMap) -> Type -> Type
extract_type_type _ _ (JST0_Int) = JST0_Int
extract_type_type _ _ (JST0_Bool) = JST0_Bool
extract_type_type s m (JST0_Object a mem) = (JST0_Object a (extract_type_members s m mem))
extract_type_type _ _ (JST0_String st) = (JST0_String st)
extract_type_type s m (JST0_TV a _ann) = extract_type s m a
extract_type_type _ _ (JST0_Alpha a) = (JST0_Alpha a)
extract_type_type _ _ (JST0_None) = JST0_None
extract_type_type s m (JST0_Ret t) = JST0_Ret (extract_type_type s m t)
extract_type_type s m (JST0_Function t1 t2 t3) = (JST0_Function
                                                  (extract_type_type s m t1)
                                                  (extract_type_type_list s m t2)
                                                  (extract_type_type s m t3))

extract_type_type_list :: (Set Int) -> (HL_Map,CMap) -> [Type] -> [Type]
extract_type_type_list s m ts = Prelude.map (\t -> extract_type_type s m t) ts 

-- What's the full solution for this member type given these constraints
-- -> replace all typeVariables in this type by the approropriate solution
extract_type_member :: (Set Int) -> (HL_Map,CMap) -> (Type,FieldType) -> (Type,FieldType)
extract_type_member s m (t,ft) = (extract_type_type s m t,ft)
                                                 
-- extract the type of the member fields
-- i.e. get the appropriate type for all member types
extract_type_members :: (Set Int) -> (HL_Map,CMap) -> Members -> Members
extract_type_members s m mem = Map.map (extract_type_member s m) mem

-- extract the type of a function from the constraints
-- Arguments:
--  - Set of already bound Alpha indices
--  - Higher level types map
--  - Currently infered TV index
--  - All constraints concerning that TV
-- Returns: Type of this TV
extract_type_function :: (Set Int) -> (HL_Map,CMap) -> Int -> CSet -> Type
extract_type_function s mp i cs = Map.foldr (\this rest -> extract_type_from_constraint s mp i this rest) (JST0_Function JST0_None [] JST0_None) cs

extract_type_return :: (Set Int) -> (HL_Map,CMap) -> Int -> CSet -> Type
extract_type_return s mp i cs = Map.foldr (\c prv -> extract_type_from_constraint s mp i c prv) (JST0_Ret JST0_None) cs

--TODO: Do we need to think about typing rules t'<t to derive types for t?
-- extract the type of an object from the constraints
-- Arguments:
--  - Set of already bound Alpha indices
--  - Higher level types map
--  - Currently infered TV index
--  - All constraints concerning that TV
-- Returns: Type of this TV (TV less)
extract_type_object :: (Set Int) -> (HL_Map,CMap) -> Int -> CSet -> Type
extract_type_object s mp i cs | trace 35 ("Extracting object: mu " ++ show (Beta i)) False = undefined
extract_type_object s mp i cs = Map.foldr (\this rest -> extract_type_from_constraint s mp i this rest) (object_empty (Beta i)) cs

-- Returns upper bound for the type TV with the given index
extract_type_from_constraint :: (Set Int) -> (HL_Map,CMap) -> Int -> Constrain -> Type -> Type
extract_type_from_constraint s mp i c t |trace 35 ("extract_type_from_constraint: " ++ show i ++ ":" ++ show c ++ " working solution: " ++ show t) False = undefined
extract_type_from_constraint s mp i (SubType (JST0_TV a _ann) t) tc |  (a == i) =
  case t of
    (JST0_TV _a _ann) -> tc -- indirect subtypings have been handled by closure
    (JST0_Alpha _) -> tc
    (JST0_Object NotRec mem) -> min_type (JST0_Object (Beta i) (extract_type_members s mp mem)) tc
    _ -> min_type (extract_type_type s mp t) tc
extract_type_from_constraint s mp i (Extend (JST0_TV a _ann) t) tc | (a == i) =
  case t of
    (JST0_TV _a _ann) -> tc
    (JST0_Alpha _) -> tc
    _ -> min_type (extract_type_type s mp t) tc
extract_type_from_constraint s mp i (MemberExtend (JST0_TV a _ann) m t) tc | (a == i) =
  case t of
    (JST0_TV _a _ann) -> tc -- indirect constraints have been checked using closure
    (JST0_Alpha _) -> tc
    _ -> min_type (object_set_field_type (extract_type_type s mp t) m Definite) tc
extract_type_from_constraint _s _mp _i _c tc = tc
-- empty, only and only_type is checked afterwards
-- any other constraint is not relevant


----------------------------------------
-- Check the solution fulfils the upper bounds
----------------------------------------

check_solution :: [Constrain] -> Solution -> Bool
check_solution [] sol = True
check_solution (c:cs) sol = let
  cm = lookup_constrain c sol
  in check_constrain_single cm

lookup_constrain :: Constrain -> Solution -> Constrain
lookup_constrain (SubType t1 t2) sol = SubType (lookup_type t1 sol) (lookup_type t2 sol)

lookup_type :: Type -> Solution -> Type
lookup_type (JST0_TV a _ann) sol = solution_get sol a
lookup_type t _sol= t

get_upper_bounds :: [Constrain] -> [Constrain]
get_upper_bounds [] = []
get_upper_bounds (c:cs) = let r = get_upper_bounds cs
                          in case c of
                            (Empty t) -> c:r
                            (Only _ _) -> c:r
                            (Only_type _ _) -> c:r
                            _ -> r
                            
