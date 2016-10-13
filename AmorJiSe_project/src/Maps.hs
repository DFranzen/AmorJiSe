module Maps where

import Data.Map as Map
import Data.Set as Set

import JST0_types
import JST0_constrain

----------------------------------------
-- Higher Level Map
--  save the HL type of each TV
----------------------------------------

type HL_Map = Map Int HL_Type

hl_map_set :: HL_Map -> Type -> HL_Type -> HL_Map
hl_map_set m (JST0_TV a _ann) t = hl_map_seti m a t

hl_map_seti :: HL_Map -> Int -> HL_Type -> HL_Map
hl_map_seti m a t = let
  cur = Map.lookup a m
  new = case cur of
    Nothing -> t
    Just told -> (add_HL_types told t)
  in Map.insert a new m

hl_map_set_set :: HL_Map -> Set Int -> HL_Type -> HL_Map
hl_map_set_set m s t = Set.fold (\a ma -> hl_map_seti ma a t) m s

hl_map_get :: HL_Map -> Type -> HL_Type
hl_map_get m (JST0_TV a _ann) = hl_map_geti m a

hl_map_geti :: HL_Map -> Int -> HL_Type
hl_map_geti m a = case Map.lookup a m of
  Just t -> t
  Nothing -> HL_None

--return the HL_type either from the map, or from the type itself
hl_get :: HL_Map -> Type -> HL_Type
hl_get m (JST0_TV a _ann) = hl_map_geti m a
hl_get _m t = get_HL_type t

hl_map_consistent :: HL_Map -> Type -> HL_Type -> Bool
hl_map_consistent m t ht = let
  hlt = hl_get m t
  in hlt == ht

hl_map_consistenti :: HL_Map -> Int -> HL_Type -> Bool
hl_map_consistenti m a ht = let
  hlt = hl_map_geti m a
  in hlt==ht

hl_map_consistent_pair :: HL_Map -> Type -> Type -> Bool
hl_map_consistent_pair m t1 t2 = let
  ht1 = hl_get m t1
  ht2 = hl_get m t2
  in ht1 == ht2
     
hl_map_consistent_pairi :: HL_Map -> Int -> Int -> Bool
hl_map_consistent_pairi m a1 a2 = let
  hlt1 = hl_map_geti m a1
  hlt2 = hl_map_geti m a2
  in hlt1 == hlt2

----------------------------------------
-- Constraint Set
--   save all the constraints without duplicates
----------------------------------------

type CSet = Map String Constrain

-- return true if the constraints map is empty
cset_is_empty :: CSet -> Bool
cset_is_empty s = Map.null s

cset_empty :: CSet
cset_empty = Map.empty

cset_insert :: CSet -> Constrain -> CSet
cset_insert cs c = Map.insert (show c) c cs

cset_check_and_insert :: CSet -> Constrain -> (Bool,CSet)
cset_check_and_insert cs c = let
  prev = cset_contains cs c
  nset | prev = cs
       | otherwise = cset_insert cs c
  in (prev,nset)

-- insert multiple Constraints into an existing Constraints Map
cset_insert_multi :: CSet -> [Constrain] -> CSet
cset_insert_multi cs c = Prelude.foldr (\c cs -> cset_insert cs c) cs c

-- Convert a Map of Constraints into an easier to handle list.
cset_to_list :: CSet -> [Constrain]
cset_to_list m = Map.elems m

-- Convert a List of Constraints into a Map, so we don't get duplicates
cset_from_list :: [Constrain] -> CSet
cset_from_list cs = (cset_insert_multi cset_empty cs)

-- Check if a ConMap contains the given constrain
cset_contains :: CSet -> Constrain -> Bool
cset_contains m c = case Map.lookup (show c) m of
  (Just _) -> True
  Nothing -> False

-- union with check, how many of the elements from the 1st argument were inserted into the 2nd argument
cset_union_int :: CSet -> CSet -> (CSet, Int)
cset_union_int cm cmp = let
  cmp_c = Map.size cmp
  un = Map.union cm cmp
  un_c = Map.size un
  in (un,un_c-cmp_c)


-- insert with check, if it is already in there
-- Return:
--  - True if new constraints were inserted
--  - False if they already existed

cset_union_bool :: CSet -> CSet -> (CSet, Bool)
cset_union_bool cm cmp = let cs= cset_to_list cm
                          in Prelude.foldr (cset_insert_bool) (cmp,False) cs

cset_insert_bool :: Constrain -> (CSet,Bool) -> (CSet,Bool)
cset_insert_bool c (cm,b) = let bn = b || not(cset_contains cm c)
                                cmn = cset_insert cm c
                            in (cmn,bn)

----------------------------------------
-- Constraint Map
--   save all the constraints affecting each type variable
----------------------------------------

type CMap = Map Int (CSet)

cmap_empty :: CMap
cmap_empty = Map.empty

-- Add a constrain to the sorted constrain set
--  -> add to the list if index is already there
--  -> add new key with a singleton list, if not there yet
cmap_addWithType :: CMap -> Type -> Constrain -> CMap
cmap_addWithType m (JST0_TV a1 _ann1) c = let
  cur = cmap_geti m a1
  new = cset_insert cur c
  in Map.insert a1 new m
cmap_addWithType m _ _ = m

cmap_addi :: CMap -> Int -> Constrain -> CMap
cmap_addi cm i c = let
  cur = cmap_geti cm i
  new = cset_insert cur c
  in Map.insert i new cm

cmap_addWithIndexSet :: CMap -> Set Int -> Constrain -> CMap
cmap_addWithIndexSet cm is c = Set.fold (\i prv -> cmap_addi prv i c) cm is

cmap_add :: CMap -> Constrain -> CMap
cmap_add cmap c = let
  is = cmap_where_all c
  in cmap_addWithIndexSet cmap is c
  
  
--  case c of 
--  (Empty t) -> cmap_addWithType cmap t c
--  (SubType t1 t2) -> cmap_addWithType (cmap_addWithType cmap t1 c) t2 c
--  (IsObject t) -> cmap_addWithType cmap t c
--  (MemberExtend t _ t2) -> cmap_addWithType (cmap_addWithType cmap t2 c) t c
--  (Extend t1 t2) -> cmap_addWithType (cmap_addWithType cmap t1 c) t2 c
--  (Only t1 _) -> cmap_addWithType cmap t1 c
--  (Only_type t1 t2) -> cmap_addWithType (cmap_addWithType cmap t1 c) t2 c

cmap_check_and_insert :: CMap -> Constrain -> (CMap,Bool)
cmap_check_and_insert cm c = let
  b = cmap_contains cm c
  cm_new | b = cm
         | otherwise = cmap_add cm c
  in (cm_new,b)

cmap_from_list :: [Constrain] -> CMap
cmap_from_list [] = Map.empty
cmap_from_list (c:s) = let r = cmap_from_list s
                       in cmap_add r c

cmap_geti :: CMap -> Int -> CSet
cmap_geti cmap tv = case Map.lookup tv cmap of
  Nothing -> cset_empty
  Just t -> t

cmap_contains :: CMap -> Constrain -> Bool
cmap_contains cm c = let
  -- get one of the indices c could be saved in
  i = cmap_where_one c
  cur = cmap_geti cm i
  in cset_contains cur c

cmap_where_one :: Constrain -> Int
cmap_where_one c | tv_rel c = JST0_constrain.tv_rel_get c
                 | otherwise = -1

cmap_where_all :: Constrain -> Set Int
cmap_where_all c | tv_rel c = JST0_constrain.tv_rel_get_all c
                 | otherwise = Set.insert (-1) Set.empty

cmap_size :: CMap -> Int
cmap_size cm = Map.size cm

----------------------------------------
-- TypeVariable map
--   Save the related TVs for each TV
----------------------------------------

type TVMap = Map Int (Set Int)

tvmap_empty :: TVMap
tvmap_empty = Map.empty

tvmap_add :: TVMap -> Type -> Type -> TVMap
tvmap_add m (JST0_TV a1 _ann1) (JST0_TV a2 _ann2) = let
  cur = Map.lookup a1 m
  new = case cur of
    Nothing -> Set.singleton a2
    (Just cs) -> Set.insert a2 cs
  in Map.insert a1 new m
tvmap_add m _ _ = m

tvmap_add_pair :: TVMap -> Type -> Type -> TVMap
tvmap_add_pair m t1 t2 = tvmap_add (tvmap_add m t1 t2) t2 t1

tvmap_add_constrain :: TVMap -> Constrain -> TVMap
tvmap_add_constrain tm c = case c of
                           (Empty _t) -> tm
                           (SubType t1 t2) -> tvmap_add_pair tm t1 t2
                           (MemberExtend t1 _ t2) -> tvmap_add_pair tm t1 t2
                           (Extend t1 t2) -> tvmap_add_pair tm t1 t2
                           (IsObject _t) -> tm
                           (Only _t _s) -> tm
                           (Only_type t1 t2) -> tvmap_add_pair tm t1 t2


tvmap_from_list :: [Constrain] -> TVMap
tvmap_from_list [] = Map.empty
tvmap_from_list (c:cs) = let r = tvmap_from_list cs
                         in tvmap_add_constrain r c

tvmap_from_CMap :: CMap -> TVMap
tvmap_from_CMap cm = Map.fold (\cs prv -> tvmap_add_from_CSet prv cs) tvmap_empty cm

tvmap_add_from_CSet :: TVMap -> CSet -> TVMap
tvmap_add_from_CSet tm cs = Map.fold (\c prv -> tvmap_add_constrain prv c) tm cs

tvmap_geti :: TVMap -> Int -> Set Int
tvmap_geti tvmap tv = case Map.lookup tv tvmap of
  Nothing -> Set.empty
  Just t -> t
