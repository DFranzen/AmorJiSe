module JST0P_constrain where

import JST0P_types
import JST0_type_aux
import JST0P_solution

import Data.Map as Map
import Data.Set as Set

import Debugging

-- Annotated constraints
-- TODO think where we actually need them
data ConstrainAn = Gt [Annotation] [Annotation]
                 | Eq [Annotation] [Annotation]
                 deriving Eq

instance Ord ConstrainAn where
  compare (Gt _ _) (Eq _ _) = GT
  compare (Eq _ _) (Gt _ _) = LT
  compare (Gt a b) (Gt c d) | a > c = GT
                            | c > a = LT
                            | otherwise = compare b d
  compare (Eq a b) (Eq c d) | a > c = GT
                            | c > a = LT
                            | otherwise = compare b d

instance Show ConstrainAn where
  show (Gt s1 s2) = (show_sum s1) ++ ">=" ++ (show_sum s2) ++ "\n"
  show (Eq s1 s2) = (show_sum s1) ++ "=" ++ (show_sum s2) ++ "\n"

-- show a sum represented as the list of summands
show_sum :: [Annotation] -> String
show_sum ([]) = "0"
show_sum [x] = (show x)
show_sum (x:xs) = (show x) ++ "+" ++ (show_sum xs)

----------------------------------------
-- compares two annotated types and returns a list of compared pairs according to comparison function
-- arguments:
--   - Annotation selector for lhs
--   - Annotation operator
--   - Annotation selector for rhs
--   - lhs
--   - rhs
--   - set of constraints before this step
----------------------------------------
type AnnotationPair = (Annotation,Annotation)
type Comp_Selector = AnnotationPair -> [Annotation]
type Comp_Operator = Annotation -> Annotation -> ConstrainAn

comp_eq :: Comp_Operator
comp_eq e1 e2 = Eq [e1] [e2]

comp_gt :: Comp_Operator
comp_gt e1 e2 = Gt [e1] [e2]

comp_all :: Comp_Selector
comp_all (a1,a2) = [a1,a2]

comp_nu :: Comp_Selector
comp_nu (a1,a2) = [a1]

comp_n :: Comp_Selector
comp_n (a1,a2) = [a2]

sel2Set :: [Annotation] -> [Annotation] -> Comp_Operator -> Set ConstrainAn
sel2Set [] [] _ = Set.empty
sel2Set (x:xs) (y:ys) op = Set.insert (op x y) (sel2Set xs ys op)

calc_constraints :: AnnotationPair -> Comp_Selector -> Comp_Operator -> Comp_Selector -> AnnotationPair -> Set ConstrainAn
calc_constraints ap1 s1 op s2 ap2  = sel2Set (s1 ap1) (s2 ap2) op

compare_Member :: Comp_Selector -> Comp_Operator -> Comp_Selector -> (TypeAn, FieldType) -> (TypeAn, FieldType) -> Set ConstrainAn -> Set ConstrainAn
compare_Member s1 op s2 (t1,ft1) (t2,ft2) cs = compare_An s1 op s2 t1 t2 cs

compare_Members :: Comp_Selector -> Comp_Operator -> Comp_Selector -> (MembersAn) -> (MembersAn) -> Set ConstrainAn -> Set ConstrainAn
compare_Members s1 op s2 t1 t2 cs | trace 30 ("compare_Members " ++ show t1 ++ "," ++ show t2) False = undefined
compare_Members s1 op s2 mem1 mem2 cs = Map.foldrWithKey
                                        (\k t c -> (compare_Member s1 op s2 (membersAn_get mem1 k) t c)) 
                                        cs 
                                        mem2

compare_An :: Comp_Selector -> Comp_Operator -> Comp_Selector -> TypeAn -> TypeAn-> Set ConstrainAn -> Set ConstrainAn
compare_An s1 op s2 t1 t2 cs | trace 30 ("compare_An " ++ show t1 ++ "," ++ show t2) False = undefined
compare_An s1 op s2 (t1,nu1,n1) (t2,nu2,n2) cs = let (cs2,b2) = union_and_test (calc_constraints (nu1,n1) s1 op s2 (nu2,n2)) cs
                                                     back | b2 = compare_P s1 op s2 t1 t2 cs2
                                                          | otherwise = cs
                                                 in back

compare_P :: Comp_Selector -> Comp_Operator -> Comp_Selector  -> TypeP -> TypeP -> Set ConstrainAn -> Set ConstrainAn
compare_P s1 op s2 t1 t2 cs | trace 30 ("compare_P " ++ show t1 ++ "," ++ show t2) False = undefined
compare_P s1 op s2 (JST0P_Object a1 mem1) (JST0P_Object a2 mem2) cs = 
  let 
      meme1 = membersAn_subs_alpha mem1 a1 (JST0P_Object a1 mem1)
      meme2 = membersAn_subs_alpha mem2 a2 (JST0P_Object a2 mem2)
  in compare_Members s1 op s2 meme1 meme2 cs
compare_P s1 op s2 (JST0P_Function o1 xs1 n1 r1 np1) (JST0P_Function o2 xs2 n2 r2 np2) cs = 
  let 
      cs1 = compare_An   comp_all comp_eq comp_all o1  o2  cs
      cs2 = compare_list comp_all comp_eq comp_all xs1 xs2 cs1
      cs3 = compare_An   comp_all comp_eq comp_all r1  r2  cs2
  in Set.union cs3 (Set.fromList [Eq [n1] [n2],Eq [np1] [np2]])
compare_P s1 op s2 JST0P_Int JST0P_Int cs = cs
compare_P s1 op s2 JST0P_Bool JST0P_Bool cs = cs
compare_P s1 op s2 (JST0P_String _s) (JST0P_String _s2) cs = cs
compare_P s1 op s2 (JST0P_Ret t1) (JST0P_Ret t2) cs = compare_An s1 op s2 t1 t2 cs
compare_P s1 op s2 (JST0P_None) (JST0P_None) cs = cs
-- compare_P l1 l2 l3 (JST0P_Alpha) should never happen, since objects are unfolded all the time.

compare_list :: Comp_Selector -> Comp_Operator -> Comp_Selector -> [TypeAn] -> [TypeAn] -> Set ConstrainAn -> Set ConstrainAn
compare_list s1 op s2 [] [] cs = cs --If the 
compare_list s1 op s2 (x:xs) (y:ys) cs = let cs1 = compare_An s1 op s2 x y cs
                                         in compare_list s1 op s2 xs ys cs1

compareT :: Comp_Selector -> Comp_Operator -> Comp_Selector -> TypeAn -> TypeAn -> Set ConstrainAn
compareT s1 op s2 t1 t2 | trace 30 ("compareT " ++ show t1 ++ "," ++ show t2) False = undefined
compareT s1 op s2 t1 t2 = let
        (dt1,i1,ma1) = distingtify_An (t1,0,Map.empty)
        (dt2,_,ma2) = distingtify_An (t2,i1,ma1)
        back |trace 30 ("comparing " ++ show dt1 ++ "," ++ show dt2) True = compare_An s1 op s2 dt1 dt2 Set.empty
        in undistingtify_constraintsAn back ma2

----------------------------------------
-- insert a new element into a set and also return if it was a new item
----------------------------------------
insert_and_test :: ConstrainAn -> Set ConstrainAn -> (Set ConstrainAn,Bool)
insert_and_test new set | trace 30 ("insert_and_test " ++ show new ++ "," ++ show set) False = undefined
insert_and_test new set = (Set.insert new set,not (Set.member new set))


----------------------------------------
-- return true if one element from the first set was new in the second set
----------------------------------------
union_and_test :: Set ConstrainAn -> Set ConstrainAn -> (Set ConstrainAn,Bool)
union_and_test new set | trace 30 ("union_and_test " ++ show new ++ "," ++ show set) False = undefined
union_and_test cs1 cs2 = Set.foldr (\c (cs,b) -> let (csp,bp) = insert_and_test c cs
                                                 in (csp,b || bp)
                                   ) (cs2,False) cs1

----------------------------------------
-- Create constraints so that the relation T1^nu/N <= T2^nu/N
----------------------------------------

makeEqualAn_nu_nu :: TypeAn -> TypeAn -> Set ConstrainAn
makeEqualAn_nu_nu = compareT comp_nu comp_eq comp_nu

makeEqual_nu_nu :: TypeAn -> TypeAn -> [ConstrainAn]
makeEqual_nu_nu t1 t2 | trace 30 ("Computing constraints for nu nu " ++ show t1 ++ " " ++ show t2) False = undefined
makeEqual_nu_nu t1 t2 = Set.toList (makeEqualAn_nu_nu t1 t2)

makeEqualAn_n_n :: TypeAn -> TypeAn -> Set ConstrainAn
makeEqualAn_n_n = compareT comp_n comp_eq comp_n

makeEqual_n_n :: TypeAn -> TypeAn -> [ConstrainAn]
makeEqual_n_n t1 t2 | trace 30 ("Computing constraints for n n " ++ show t1 ++ " " ++ show t2) False = undefined
makeEqual_n_n t1 t2 = Set.toList (makeEqualAn_n_n t1 t2)

makeGreater_nu_nu :: TypeAn -> TypeAn -> Set ConstrainAn
makeGreater_nu_nu = compareT comp_nu comp_gt comp_nu

makeGreater_n_n :: TypeAn -> TypeAn -> Set ConstrainAn
makeGreater_n_n = compareT comp_n comp_gt comp_n

makeLess_nu_nu :: TypeAn -> TypeAn -> Set ConstrainAn
makeLess_nu_nu t1 t2 = makeGreater_nu_nu t2 t1

makeLess_n_n :: TypeAn -> TypeAn -> Set ConstrainAn
makeLess_n_n t1 t2 = makeGreater_n_n t2 t1

makeEqualAn_all :: TypeAn -> TypeAn -> Set ConstrainAn
makeEqualAn_all = compareT comp_all comp_eq comp_all

makeEqual_all :: TypeAn -> TypeAn -> [ConstrainAn]
makeEqual_all t1 t2 | trace 30 ("Computing constraints for nu and n " ++ show t1 ++ " " ++ show t2) False = undefined
makeEqual_all t1 t2 = Set.toList (makeEqualAn_all t1 t2)

makeEqualAn_nu_n :: TypeAn -> TypeAn -> Set ConstrainAn
makeEqualAn_nu_n = compareT comp_nu comp_eq comp_n

makeEqual_nu_n :: TypeAn -> TypeAn -> [ConstrainAn]
makeEqual_nu_n t1 t2 | trace 30 ("Computing constraints for nu to n " ++ show t1 ++ " " ++ show t2) False = undefined
makeEqual_nu_n t1 t2 = Set.toList (makeEqualAn_nu_n  t1 t2)


----------------------------------------
-- create constraints such that all resources are equal except for in the type of field m
----------------------------------------
makeExtendAn :: String -> TypeAn -> TypeAn -> Set ConstrainAn
makeExtendAn m ((JST0P_Object a1 mem1),nu1,n1) ((JST0P_Object a2 mem2),nu2,n2) = 
  let meme1 = membersAn_subs_alpha mem1 a1 (JST0P_Object a1 mem1)
      meme2 = membersAn_subs_alpha mem2 a2 (JST0P_Object a2 mem2)
      cs = makeExtend_Members m meme1 meme2
  in Set.union cs (Set.fromList [Eq [nu1] [nu2],Eq [n1] [n2]])

makeExtend :: String -> TypeAn -> TypeAn -> [ConstrainAn]
makeExtend s t1 t2 | trace 30 ("Computing Extend constraints: " ++ show t1 ++ " " ++ s ++ " " ++ show t2) False = undefined
makeExtend s t1 t2 = Set.toList (makeExtendAn s t1 t2)


makeExtend_Members :: String -> MembersAn -> MembersAn -> Set ConstrainAn
makeExtend_Members m mem1 mem2 = Map.foldrWithKey
                                 (\k t c -> Set.union (makeExtendAn_Member m k mem1 mem2) c)
                                 Set.empty
                                 mem1


makeExtendAn_Member :: String -> String -> MembersAn -> MembersAn -> Set ConstrainAn
makeExtendAn_Member m m1 mem1 mem2 | m == m1 = Set.empty
                                   | otherwise = let
                                                  (t1,psi1) = membersAn_get mem1 m1
                                                  (t2,psi2) = membersAn_get mem2 m1
                                               in makeEqualAn_all t1 t2

makeExtend_Member :: String -> String -> MembersAn -> MembersAn -> [ConstrainAn]
makeExtend_Member m m1 t1 t2 | trace 30 ("Computing Extend member constraints: " ++ show t1 ++ " " ++ m ++ " " ++ show t2) False = undefined
makeExtend_Member m m1 mem1 mem2 = Set.toList (makeExtendAn_Member m m1 mem1 mem2)

----------------------------------------
-- compute Constraints to make two types subtypes
----------------------------------------

makeSubtypeAn :: TypeAn -> TypeAn -> Set ConstrainAn
makeSubtypeAn t1 t2 = Set.union (makeLess_n_n t1 t2) (makeGreater_nu_nu t1 t2)

makeSubtype :: TypeAn -> TypeAn -> [ConstrainAn]
makeSubtype t1 t2 | trace 30 ("Computing Subtype constraints: " ++ show t1 ++ "," ++ show t2) False = undefined
makeSubtype t1 t2 = Set.toList (makeSubtypeAn t1 t2)

makeSubtype_list :: [TypeAn] -> [TypeAn] -> [ConstrainAn]
makeSubtype_list t1 t2 | trace 30 ("Computing Subtype list constraints: " ++ show t1 ++ "," ++ show t2) False = undefined
makeSubtype_list [] [] = []
makeSubtype_list (x:xs) (y:ys) =  (Set.toList (makeSubtypeAn x y)) ++ (makeSubtype_list xs ys)

----------------------------------------
-- Compute set of Constraints to make the three types match the Split definition
-- enforces t1 -> t2 (+) t3
----------------------------------------

makeSplit_Member :: (TypeAn,FieldType) -> (TypeAn,FieldType) -> (TypeAn,FieldType) -> Set ConstrainAn -> Set ConstrainAn
makeSplit_Member (t1,f1) (t2,f2) (t3,f3) cs = makeSplit_An t1 t2 t3 cs

makeSplit_P :: TypeP -> TypeP -> TypeP -> Set ConstrainAn -> Set ConstrainAn
makeSplit_P t1 t2 t3 cs | trace 30 ("makeSplitP " ++ show t1 ++ "->" ++ show t2 ++ "(+)" ++ show t3) False = undefined
makeSplit_P (JST0P_Object a1 mem1) (JST0P_Object a2 mem2) (JST0P_Object a3 mem3) cs = let
  -- unfold the Object types
  uf1 = membersAn_subs_alpha mem1 a1 (JST0P_Object a1 mem1)
  uf2 = membersAn_subs_alpha mem2 a2 (JST0P_Object a2 mem2)
  uf3 = membersAn_subs_alpha mem3 a3 (JST0P_Object a3 mem3)
  in makeSplit_Members uf1 uf2 uf3 cs
makeSplit_P JST0P_Int JST0P_Int JST0P_Int cs = cs
makeSplit_P JST0P_Bool JST0P_Bool JST0P_Bool cs = cs
makeSplit_P (JST0P_String s1) (JST0P_String s2) (JST0P_String s3) cs = cs
makeSplit_P (JST0P_Ret t1) (JST0P_Ret t2) (JST0P_Ret t3) cs = makeSplit_An t1 t2 t3 cs
makeSplit_P (JST0P_Function o1 xs1 n1 r1 np1) (JST0P_Function o2 xs2 n2 r2 np2) (JST0P_Function o3 xs3 n3 r3 np3) cs = 
  let
    cs2 = compare_P comp_all comp_eq comp_all (JST0P_Function o1 xs1 n1 r1 np1) (JST0P_Function o3 xs3 n3 r3 np3) cs
  in compare_P comp_all comp_eq comp_all (JST0P_Function o1 xs1 n1 r1 np1) (JST0P_Function o2 xs2 n2 r2 np2) cs2            

makeSplit_An :: TypeAn -> TypeAn -> TypeAn -> Set ConstrainAn-> Set ConstrainAn
makeSplit_An (t1,nu1,n1) (t2,nu2,n2) (t3,nu3,n3) cs = let (cs2,b2) = union_and_test (Set.fromList [Gt [nu1] [nu2,nu3], Eq [n1] [n2],Eq [n1] [n3]]) cs
                                                          back | b2 = makeSplit_P t1 t2 t3 cs2
                                                               | otherwise = cs
                                                      in back

makeSplit_Members :: MembersAn -> MembersAn -> MembersAn -> Set ConstrainAn -> Set ConstrainAn
makeSplit_Members mem1 mem2 mem3 cs | ((Map.keysSet mem1) == (Map.keysSet mem2)) && ((Map.keysSet mem2) == (Map.keysSet mem3)) =
  Map.foldrWithKey
  (\k t c -> makeSplit_Member (membersAn_get mem1 k) (membersAn_get mem2 k) t c)
  cs
  mem3

makeSplit :: TypeAn -> TypeAn -> TypeAn -> [ConstrainAn]
makeSplit t1 t2 t3 | trace 30 ("makeSplit " ++ (show t1) ++ " " ++ (show t2) ++ " " ++ (show t3)) False = undefined
makeSplit t1 t2 t3 = let
        (dt1,i1,ma1) = distingtify_An (t1,0,Map.empty)
        (dt2,i2,ma2) = distingtify_An (t2,i1,ma1)
        (dt3,_ ,ma3) = distingtify_An (t3,i2,ma2)
        back = makeSplit_An dt1 dt2 dt3 Set.empty
        in Set.toList (undistingtify_constraintsAn back ma3)

----------------------------------------
-- compute the type of a sequence of expressions.
----------------------------------------
-- The result will usually be the type of the 2nd expression, except if the first expression is a return expression
-- Arguments:
--   - next index for a TV
--   - next index for an annotation
--   - resources available before the execution of the sequence
--   - Type of 1st expression
--   - Type of 2nd expression
-- Returns:
--   - Next index for a TV
--   - Next index for an annotation
--   - resources available after concatenation
--   - Type of concatenation
----------------------------------------
seq_typeP :: (Int,SolutionAn) -> TypeP -> TypeP -> (Int,TypeP,[ConstrainAn])
seq_typeP (a,sol) (JST0P_Ret t1) (JST0P_Ret t2) = let
  t = solutionAn_get sol a
  c1 = Set.toList (makeSubtypeAn t t1)
  c2 = Set.toList (makeSubtypeAn t t2)
  in (a+1,JST0P_Ret t,concat [c1,c2])
seq_typeP (a,sol) (JST0P_Ret t1) _t2 | error "Return on some paths only" = (a,JST0P_Ret t1,[])
seq_typeP (a,sol) _t1 t2 = (a,t2,[])

seq_typeAn :: (Int,SolutionAn) -> TypeAn -> TypeAn -> (Int,TypeAn,[ConstrainAn])
seq_typeAn (a,sol) (t1,_,_) (t2,_,_) = let 
    (a,t,c) = seq_typeP (a,sol) t1 t2
  in (a,(t,I 0,I 0),c)
----------------------------------------
-- Compute set of Constraints to make the three types match the minimum Relation
--  o3 = min(o1,o2)
-- Prerequisite: 
--   - All types in o3 are (pure) subtypes of the equivalent types in o1 and in o2 (garanteed by ConstGen)
----------------------------------------

makeMin :: TypeAn -> TypeAn -> TypeAn -> [ConstrainAn]
makeMin t1 t2 t3 | trace 30 ("Computing minimum constraints " ++ show t1 ++ "," ++ show t2 ++ "," ++ show t3) False = undefined
makeMin t1 t2 t3 = Set.toList( Set.union (Set.union (makeEqualAn_n_n t3 t1) (makeLess_nu_nu t3 t1)) (Set.union (makeEqualAn_n_n t3 t2) (makeLess_nu_nu t3 t2)))

----------------------------------------
-- Compute a set of constraints that guarantees, that the given type does not hold any usable resource tickets (in the first annotation)
----------------------------------------
makeEmpty_P :: TypeP -> Set ConstrainAn
makeEmpty_P (JST0P_Object _alpha mem) = makeEmpty_Members mem
makeEmpty_P _ = Set.empty

makeEmpty_An :: TypeAn -> Set ConstrainAn
makeEmpty_An (t,nu,n) = Set.insert (Eq [I 0] [nu]) (makeEmpty_P t)

makeEmpty_Members :: MembersAn -> Set ConstrainAn
makeEmpty_Members mem = Map.fold (\(t,_ft) r -> Set.union r (makeEmpty_An t)) Set.empty mem 

makeEmpty :: TypeAn -> [ConstrainAn]
makeEmpty t | trace 30 ("Computing empty constraints " ++ show t) False = undefined
makeEmpty t = Set.toList (makeEmpty_An t)

----------------------------------------
-- auxiliary functions
----------------------------------------

undistingtify_constrainAn :: ConstrainAn -> Map Int Int -> ConstrainAn
undistingtify_constrainAn (Gt n1 n2) ma = Gt (undistingtify_Annotations n1 ma) (undistingtify_Annotations n2 ma)
undistingtify_constrainAn (Eq n1 n2) ma = Eq (undistingtify_Annotations n1 ma) (undistingtify_Annotations n2 ma)
undistingtify_constraintsAn :: Set ConstrainAn -> Map Int Int -> Set ConstrainAn
undistingtify_constraintsAn cs ma = Set.map (\c -> undistingtify_constrainAn c ma) cs

test1 :: TypeAn
test1 = (JST0P_Object (Alpha 0) (Map.fromList [("a",((JST0P_Alpha (Alpha 0),N 4,N 5),Definite))]), N 0, N 1)

test2 :: TypeAn
test2 = (JST0P_Object (Alpha 1) (Map.fromList [("a",((
   JST0P_Object (Alpha 2) (Map.fromList [("a",((JST0P_Alpha (Alpha 1),N 14,N 16),Definite))])
   ,N 7,N 8),Definite))]), N 10, N 24)

test3 :: TypeAn
test3 = (JST0P_Object (Alpha 1) (Map.fromList [("a",((JST0P_Alpha (Alpha 1),N 17,N 18),Definite))]), N 11, N 25)

testReal1 :: TypeP
testReal1 = (JST0P_Object (Beta 20) (Map.fromList [("value",((JST0P_Int,N 2,N 3),Definite)),("next",((JST0P_Alpha (Beta 20),N 4,N 5),Definite))]))

testReal2a :: TypeP
testReal2a = (JST0P_Object (Beta 20) (Map.fromList [("value",((JST0P_Int,N 12,N 13),Definite)),("next",((JST0P_Alpha (Beta 20),N 14,N 15),Definite))]))

testReal2 :: TypeP
testReal2 = (JST0P_Object (Beta 17) (Map.fromList [("value",((JST0P_Int,N 8,N 9),Definite)),("next",((testReal2a,N 10,N 11),Definite))]))


