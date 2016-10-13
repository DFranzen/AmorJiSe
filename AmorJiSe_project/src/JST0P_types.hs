module JST0P_types
       (
         TypeP(..),
         TypeAn,
         Annotation(..),
         Annotation_type(..),
         MembersAn,

         membersAn_get,
         membersAn_get_vars,

         isTerminalType,
         isFunctionType,

--         swap_alphaP_members,
         equalize_alpha,
         equalize_alpha3,

         membersAn_subs_alpha,
         
         isSubtype_FieldType,

         objectP_empty,
         objectAn_empty,
         objectP_get,
         objectAn_get,
         objectP_set,
         objectAn_set_path,
         objectP_from_list,
         objectP_from_list_ft,

         distingtify_An,
         undistingtify_Annotation,
         undistingtify_Annotations,

         inflateP,
         inflateAn,
         deflateAn,

         is_none,
       ) where

import JST0_type_aux
import JST0_types
--import JST0P_constrain

import Data.Map as Map
import Data.Set as Set

import Debugging

--Annotation Variable
data Annotation = N Int -- variable with index
                | I Int -- constant
                deriving Eq

data Annotation_type = Nu | Ntot
                         
instance Show Annotation where
  show (N a) = "n_" ++ (show a)
  show (I a) = show a

instance Ord Annotation where
  compare (I n1) (I n2) = compare n1 n2
  compare (N n1) (N n2) = compare n1 n2
  compare (I _n1) (N _n2) = LT
  compare (N _n1) (I _n2) = GT

-- seperates a list of Annotations into one list with known and one with onknown parts
sepKnown :: [Annotation] -> ([Annotation],[Annotation])
sepKnown [] = ([],[])
sepKnown ((I n):ns) = let
  (k,u) = sepKnown ns
  in ((I n):k,u)
sepKnown ((N n):ns) = let
  (k,u) = sepKnown ns
  in (k,(N n):u)

sum_Ann :: [Annotation] -> Int
sum_Ann [] = 0
sum_Ann ((I n):ns) = n + sum_Ann ns

isEqual :: [Annotation] -> [Annotation] -> Bool
isEqual a b = (Set.fromList a) == (Set.fromList b)

isLessUnknown :: [Annotation] -> [Annotation] -> Bool
isLessUnknown a b = Set.isSubsetOf (Set.fromList a) (Set.fromList b)

isGreaterUnknown :: [Annotation] -> [Annotation] -> Bool
isGreaterUnknown a b = Set.isSubsetOf (Set.fromList b) (Set.fromList a)

isLess :: [Annotation] -> [Annotation] -> Bool
isLess n1 n2 = let
  (k1,u1) = sepKnown n1
  (k2,u2) = sepKnown n2
  in ((sum_Ann k1) <= (sum_Ann k2)) && isLessUnknown u1 u2

isGreater :: [Annotation] -> [Annotation] -> Bool
isGreater n1 n2 = let
  (k1,u1) = sepKnown n1
  (k2,u2) = sepKnown n2
  in ((sum_Ann k1) >= (sum_Ann k2)) && isGreaterUnknown u1 u2

--Annotated member lists
type MembersAn = Map String (TypeAn,FieldType)

----------------------------------------
-- Functions for Members
----------------------------------------

showMembersAn :: MembersAn -> String
showMembersAn t = "{" ++ (Map.foldWithKey (\s ty prv -> prv ++ (showMemberAn s ty)) "" t) ++ "}"

showMemberAn :: String -> (TypeAn,FieldType) -> String
showMemberAn s (t,tf) = (show s) ++ ":" ++ (show t) ++ (show tf) ++ ","

membersAn_empty :: MembersAn
membersAn_empty = Map.empty

membersAn_set :: MembersAn -> String -> (TypeAn,FieldType) -> MembersAn
membersAn_set m s (t,tf) = Map.insert s (t,tf) m

membersAn_set_path :: MembersAn -> Path -> (TypeAn,FieldType) -> MembersAn
membersAn_set_path m ss t | trace 30 ("membersAn_set_path " ++ show ss ++ "->" ++ show t) False = undefined
membersAn_set_path m [s] t = membersAn_set m s t
membersAn_set_path m (s:ss) t = let
  (told,f_old) = membersAn_get m s
  (_t,tf) = t
  fnew | tf == Definite = Definite
       | otherwise = f_old
  tnew = objectAn_set_path told ss t
  in membersAn_set m s (tnew,fnew)

membersAn_get :: MembersAn -> String -> (TypeAn,FieldType)
membersAn_get m s = case (Map.lookup s m) of
  Just t -> t
  Nothing -> ((JST0P_None,I 0,I 0),Potential)

membersAn_contains :: MembersAn -> String -> Bool
membersAn_contains m s = Map.member s m

membersAn_get_type :: MembersAn -> String -> TypeAn
membersAn_get_type m s = let (t,_) = membersAn_get m s
                         in t

membersAn_get_FieldType :: MembersAn -> String -> FieldType
membersAn_get_FieldType m s = let (_,f) = membersAn_get m s
                              in f

-- Checks if the two members have the same elements
membersAn_same_fields :: MembersAn -> MembersAn -> Bool
membersAn_same_fields mem1 mem2 = let
  e1 = Map.keysSet mem1
  e2 = Map.keysSet mem2
  in (e1 == e2)

--returns true if t1 has at least the fields t2 has (t1<t2)
membersAn_at_least_fields :: MembersAn -> MembersAn -> Bool
membersAn_at_least_fields mem1 mem2 = let
  e1 = Map.keysSet mem1
  e2 = Map.keysSet mem2
  in (Set.isSubsetOf e2 e1)

-- membersAn_count_pot :: MembersAn -> Int
-- membersAn_count_pot mem = Map.fold (\x i -> i+(memberAn_count_pot x)) 0 mem

-- memberAn_count_pot :: (TypeAn,FieldType) -> Int
-- memberAn_count_pot (_,Potential) = 0
-- memberAn_count_pot (t,Definite) = typeAn_count_pot t

membersAn_from_list :: [(String,TypeAn)] -> MembersAn
membersAn_from_list [] = membersAn_empty
membersAn_from_list ((s,t):xs) = membersAn_set (membersAn_from_list xs) s (t,Definite)

membersAn_from_list_ft :: [(String,TypeAn,FieldType)] -> MembersAn
membersAn_from_list_ft [] = membersAn_empty
membersAn_from_list_ft ((s,t,ft):xs) = membersAn_set (membersAn_from_list_ft xs) s (t,ft)

membersAn_get_vars :: MembersAn -> [Int]
membersAn_get_vars mem = Map.fold (\x prv -> concat [memberAn_get_vars x,prv]) [] mem

memberAn_get_vars :: (TypeAn,FieldType) -> [Int]
memberAn_get_vars (t,_tf) = typeAn_get_vars t

--Annotated Type
type TypeAn = (TypeP, Annotation, Annotation)

--Base type of an Annotated Type+
data TypeP = JST0P_Int
           | JST0P_Bool
           | JST0P_String String
             
           | JST0P_Object Recu_Variable MembersAn
           | JST0P_Alpha Recu_Variable
           | JST0P_None
             
           | JST0P_Function TypeAn [TypeAn] Annotation TypeAn Annotation
           | JST0P_Ret TypeAn

             -- | JST0P_TV Int String We should not need any type-variable in This stage anymore as we have already computed the solution for that.
           deriving Eq

instance Show TypeP where
  show (JST0P_Int) = "Int"
  show (JST0P_Bool) = "Bool"
  show (JST0P_String s)= "String(" ++ (show s) ++ ")"
  show (JST0P_Object alpha members) = "µ" ++ (show alpha) ++ ".(" ++ (showMembersAn members) ++ ")"
  show (JST0P_Function t1 t2 n1 t3 n2) = "<" ++ (show t1) ++ "⨯" ++ (show t2) ++ "," ++ (show n1) ++ "->" ++ (show t3) ++ "," ++ (show n2) ++ ">"
--  show (JST0P_TV a) = "TV_" ++ (show a)
  show (JST0P_Alpha a) = show a
  show (JST0P_Ret t) = "Return(" ++ show t ++ ")"
  show (JST0P_None) = "NONE"

isTerminalType :: TypeP -> Bool
isTerminalType JST0P_Int = True
isTerminalType JST0P_Bool = True
isTerminalType (JST0P_String _) = True
isTerminalType (JST0P_None) = True
isTerminalType _ = False

isFunctionType :: TypeP -> Bool
isFunctionType (JST0P_Function o t n tp np) = True
isFunctionType _ = False

-----------------------------
-- Inflation methods
-----------------------------

-- add annotations variables to make a TypeAn from a JST0 type
-- returns the newly annotated type and the new counter for new annotation variables.
typeAn_from_type :: Type -> Int -> (TypeAn,Int)
typeAn_from_type t a = let (ti,a1) = inflateP t a
                       in ((ti,(N a1),(N (a1+1))), a1+2)

--typeAn_from_typeP :: TypeP -> TypeAn
--typeAn_from_typeP t = (t,I 0,I 0)

--typeAn_from_typeP_list :: [TypeP] -> [TypeAn]
--typeAn_from_typeP_list = Prelude.map typeAn_from_typeP

typeAn_get_vars :: TypeAn -> [Int]
typeAn_get_vars (t,N nu,N n) = nu:(n:(typeP_get_vars t))
typeAn_get_vars (t,N nu,I n) = nu:(typeP_get_vars t)
typeAn_get_vars (t,I nu,N n) = n:(typeP_get_vars t)
typeAn_get_vars (t,I nu,I n) = typeP_get_vars t

typeAn_get_vars_list :: [TypeAn] -> [Int]
typeAn_get_vars_list ts = Prelude.foldr (\t prv -> concat [prv,typeAn_get_vars t]) [] ts

typeP_get_vars :: TypeP -> [Int]
typeP_get_vars (JST0P_Object a mem) = membersAn_get_vars mem
typeP_get_vars (JST0P_Function o t n tp np) = concat [typeAn_get_vars o,typeAn_get_vars_list t,typeAn_get_vars tp]
typeP_get_vars (JST0P_Ret t) = typeAn_get_vars t
typeP_get_vars _t = []

typeP_get_vars_list :: [TypeP] -> [Int]
typeP_get_vars_list ts = Prelude.foldr (\t prv -> concat [prv,typeP_get_vars t]) [] ts

-- add annotations to every member of the member list to create a memberlist of a JST0P object from a JST0 object
-- Arguments:
--  - members list to be annotated
--  - integer of the next annotation variable
-- Returns inflated member list and the new next index for annotation Variables
inflateMembers :: Members -> Int -> (MembersAn,Int)
inflateMembers m i = Map.foldWithKey inflateMember (membersAn_empty,i) m

inflateAn :: Type -> Int -> (TypeAn,Int)
inflateAn = typeAn_from_type

inflateAn_list :: [Type] -> Int -> ([TypeAn],Int)
inflateAn_list [] a = ([],a)
inflateAn_list (x:xs) a =
   let
     (t1,a1) = inflateAn x a
     (t2,a2) = inflateAn_list xs a1
   in (t1:t2,a2)

-- inflate and insert a field into a members+ list
-- Arguments:
--   - Key of the field to be inserted
--   - Simple type of the field
--   - Members+ list to be injected to
-- Returns: new members+ list with the inserted field
inflateMember :: String -> (Type,FieldType) -> (MembersAn,Int) -> (MembersAn,Int)
inflateMember s (t,tf) (mp,i) = let (tp,ap) = typeAn_from_type t i
                                in (membersAn_set mp s (tp,tf),ap)

-- add annotations to a JST0 type to form a TypeP
inflateP :: Type -> Int -> (TypeP,Int)
inflateP JST0_None a = (JST0P_None,a)
inflateP JST0_Int a = (JST0P_Int, a)
inflateP JST0_Bool a = (JST0P_Bool, a)
inflateP (JST0_String s) a = (JST0P_String s, a)
inflateP (JST0_Object alpha xs) a = let (xsi,ai) = inflateMembers xs a
                                    in ((JST0P_Object alpha xsi),ai)
inflateP (JST0_Alpha i) a = ((JST0P_Alpha i),a)
inflateP (JST0_Function t1 t2 t3) a = let (t1i,a1) = inflateAn t1 a
                                          (t2i,a2) = inflateAn_list t2 a1
                                          (t3i,a3) = inflateAn t3 a2
                                      in ((JST0P_Function t1i t2i (N a3) t3i (N (a3+1))),a3+2)
inflateP (JST0_Ret t) a = let
  (tp,ap) = inflateAn t a
  in (JST0P_Ret tp,ap)
-- inflateP (JST0_TV i ann) a = ((JST0P_TV i ann),a)

inflateP_list :: [Type] -> Int -> ([TypeP],Int)
inflateP_list [] a = ([],a)
inflateP_list (x:xs) a = let
  (t1,a1) = inflateP x a
  (t2,a2) = inflateP_list xs a1
  in (t1:t2,a2)

-- return the consumption of a field assign
field_consume :: FieldType -> Annotation
field_consume Definite = I 0
field_consume Potential = I 1

deflateP :: TypeP -> Type
deflateP JST0P_None = JST0_None

deflateP JST0P_Int = JST0_Int
deflateP JST0P_Bool = JST0_Bool
deflateP (JST0P_String s) = (JST0_String s)

deflateP (JST0P_Object alpha xs) = (JST0_Object alpha (deflateMembers xs))
deflateP (JST0P_Alpha i) = (JST0_Alpha i)
deflateP (JST0P_Function o t n tp np) = JST0_Function (deflateAn o) (deflateAn_list t) (deflateAn tp)
deflateP (JST0P_Ret t) = JST0_Ret (deflateAn t)

deflateP_list :: [TypeP] -> [Type]
deflateP_list = Prelude.map deflateP

deflateAn :: TypeAn -> Type
deflateAn (t,_nu,_n) = deflateP t

deflateAn_list :: [TypeAn] -> [Type]
deflateAn_list = Prelude.map deflateAn

deflateMembers :: MembersAn -> Members
deflateMembers mem = Map.map (\(t,ann) -> (deflateAn t,ann)) mem


--------------------------------------------
-- Objects
---------------------------------------------

objectP_empty :: TypeP
objectP_empty = JST0P_Object NotRec membersAn_empty

objectAn_empty :: TypeAn
objectAn_empty = (objectP_empty,I 0,I 0)

objectP_set :: TypeP -> String -> (TypeAn,FieldType) -> TypeP
objectP_set a b _ | trace 30 ("objectP_set " ++ show a ++ "." ++ show b) False = undefined
objectP_set (JST0P_Object alpha mem) s ft = (JST0P_Object alpha (membersAn_set mem s ft))
objectP_set (JST0P_None) s ft = (JST0P_Object (Alpha 0) (membersAn_set membersAn_empty s ft))

objectAn_set_path :: TypeAn -> Path -> (TypeAn,FieldType) -> TypeAn
objectAn_set_path (t,nu,n) p t2= (objectP_set_path t p t2,nu,n)

objectP_set_path :: TypeP -> Path -> (TypeAn,FieldType) -> TypeP
objectP_set_path  t1 p t2 | trace 30 ("object_set_path " ++ show p ++ "\n") False = JST0P_None
objectP_set_path (JST0P_Object a m) p t = JST0P_Object a (membersAn_set_path m p t)
objectP_set_path (JST0P_None) p t = JST0P_Object NotRec (membersAn_set_path membersAn_empty p t)

objectP_get :: TypeP -> String -> (TypeAn,FieldType)
objectP_get o m |trace 30 ("objectP_get " ++ show o ++ "," ++ show m) False = undefined
objectP_get (JST0P_Object a mem) m = let
  (t,tf) = membersAn_get mem m
  in (subs_alphaAn t a (JST0P_Object a mem),tf)
objectP_get o m | error ("Object get from non object type: " ++ show o ++ "." ++ m) = undefined
                | otherwise = undefined

objectP_get_type :: TypeP -> String -> TypeAn
objectP_get_type o m = let
  (t,_tf) = objectP_get o m
  in t

objectP_get_FieldType :: TypeP -> String -> FieldType
objectP_get_FieldType o m = let
  (_t,tf) = objectP_get o m
  in tf

objectAn_get :: TypeAn -> String -> (TypeAn,FieldType)
objectAn_get (o,nu,n) s = objectP_get o s

objectAn_get_FieldType :: TypeAn -> String -> FieldType
objectAn_get_FieldType (o,nu,n) s = objectP_get_FieldType o s

objectAn_get_type :: TypeAn -> String -> TypeAn
objectAn_get_type (o,nu,n) s = objectP_get_type o s

objectP_FieldNames :: TypeP -> Set String
objectP_FieldNames (JST0P_Object a mem) = Map.keysSet mem

objectP_from_list :: Recu_Variable -> [(String,TypeAn)] -> TypeP
objectP_from_list a l = JST0P_Object a (membersAn_from_list l)

objectP_from_list_ft :: Recu_Variable -> [(String,TypeAn,FieldType)] -> TypeP
objectP_from_list_ft a l = JST0P_Object a (membersAn_from_list_ft l)

-- exchange every occurence of the local recursive variable by the gamma variable with the given index
swap_alpha :: TypeP -> Int -> TypeP
swap_alpha t i | trace 1 ("swap_alpha " ++ show t ++ " -> " ++ show i) False = undefined
swap_alpha (JST0P_Object NotRec m) _i = JST0P_Object NotRec m
swap_alpha (JST0P_Object a m) i = JST0P_Object (Gamma i) (swap_alphaP_members m a (Gamma i))
swap_alpha t _i = t

equalize_alpha :: TypeP -> TypeP -> (MembersAn, MembersAn)
equalize_alpha (JST0P_Object a1 mem1) (JST0P_Object a2 mem2) = let
  m1 = swap_alphaP_members mem1 a1 (get_gamma a2)
  m2 = swap_alphaP_members mem2 a2 (get_gamma a2)
  in (m1,m2)

equalize_alpha3 :: TypeP -> TypeP -> TypeP -> (MembersAn, MembersAn, MembersAn)
equalize_alpha3 (JST0P_Object a1 m1) (JST0P_Object a2 m2) (JST0P_Object a3 m3) = let
  mem1 = swap_alphaP_members m1 a1 (get_gamma a3)
  mem2 = swap_alphaP_members m2 a2 (get_gamma a3)
  mem3 = swap_alphaP_members m3 a3 (get_gamma a3)
  in (mem1,mem2,mem3)


-- exchange each occurence of a1 by a2
swap_alphaP :: TypeP -> Recu_Variable -> Recu_Variable -> TypeP
swap_alphaP t a1 a2 | trace 30 ("swap_alphaP " ++ show t ++ "[" ++ show a1 ++ "->" ++ show a2 ++ "]") False = undefined
swap_alphaP (JST0P_Object a m) a1 a2 = if (a == a1)
                                       then (JST0P_Object a m)
                                       else let
                                         m_swap = swap_alphaP_members m a1 a2
                                         in JST0P_Object a m_swap
swap_alphaP (JST0P_Alpha a) a1 a2 | (a1 == a) = (JST0P_Alpha a2)
                                  | otherwise = JST0P_Alpha a
swap_alphaP (JST0P_Function t1 t2 n1 t3 n2) a1 a2 =
  JST0P_Function (swap_alphaAn t1 a1 a2) (swap_alphaAn_list t2 a1 a2) n1 (swap_alphaAn t3 a1 a2) n2
swap_alphaP t _ _ = t

swap_alphaP_list :: [TypeP] -> Recu_Variable -> Recu_Variable -> [TypeP]
swap_alphaP_list l a b = Prelude.map (\ls -> swap_alphaP ls a b) l

swap_alphaP_members :: MembersAn -> Recu_Variable -> Recu_Variable -> MembersAn
swap_alphaP_members m a1 a2 = Map.map (swap_alphaP_field a1 a2) m

swap_alphaP_field :: Recu_Variable -> Recu_Variable -> (TypeAn,FieldType) -> (TypeAn,FieldType)
swap_alphaP_field a1 a2 (t,ft) = let
  (tt,nu,n) = t
  in ((swap_alphaP tt a1 a2,nu,n),ft)

swap_alphaAn :: TypeAn -> Recu_Variable -> Recu_Variable -> TypeAn
swap_alphaAn t a1 a2 = let
  (tt,nu,n) = t
  in (swap_alphaP tt a1 a2,nu,n)

swap_alphaAn_list :: [TypeAn] -> Recu_Variable -> Recu_Variable -> [TypeAn]
swap_alphaAn_list l a b = Prelude.map (\ls -> swap_alphaAn ls a b) l

-- Substitute a recursive variable for a type
subs_alphaP:: TypeP -> Recu_Variable -> TypeP -> TypeP
subs_alphaP (JST0P_Alpha a) r t | (a == r) = t
                                | otherwise = (JST0P_Alpha a)
subs_alphaP (JST0P_Object a mem) r t | a == r = (JST0P_Object a mem)
                                     | otherwise = JST0P_Object a (membersAn_subs_alpha mem r t)
subs_alphaP (JST0P_Function o tx n tp np) r t =
  (JST0P_Function (subs_alphaAn o r t) (subs_alphaAn_list tx r t) n (subs_alphaAn tp r t) np)
subs_alphaP t _r _t = t

subs_alphaP_list :: [TypeP] -> Recu_Variable -> TypeP -> [TypeP]
subs_alphaP_list l alpha t = Prelude.map (\ls -> subs_alphaP ls alpha t) l

subs_alphaAn :: TypeAn -> Recu_Variable -> TypeP -> TypeAn
subs_alphaAn (tt,nu,n) a t = (subs_alphaP tt a t,nu,n)

subs_alphaAn_list :: [TypeAn] -> Recu_Variable -> TypeP -> [TypeAn]
subs_alphaAn_list l alpha t = Prelude.map (\ls -> subs_alphaAn ls alpha t) l

-- membersAn_subs_alpha mem a t: substitute the variable a in mem for t
membersAn_subs_alpha :: MembersAn -> Recu_Variable -> TypeP -> MembersAn
membersAn_subs_alpha mem a t | trace 30 ("membersAn_subs_alpha " ++ show mem ++ "[" ++ show a ++ "/" ++ show t ++ "]") False = undefined
membersAn_subs_alpha mem a t = Map.map (\((tm,nu,n),ft) -> ((subs_alphaP tm a t,nu,n),ft)) mem

------------------------------------------------
-- Methods to extract information about a type
------------------------------------------------

-- typeAn_count_pot :: TypeAn -> Int
-- typeAn_count_pot (t,_) = typeP_count_pot t


-- TODO: correct potential
-- typeP_count_pot :: TypeP -> Int
-- typeP_count_pot (JST0P_Int) = 1
-- typeP_count_pot (JST0P_Bool) = 1
-- typeP_count_pot (JST0P_String s) = length s
-- typeP_count_pot (JST0P_None) = 0
-- typeP_count_pot (JST0P_Alpha _) | error ("Try to count static size of recursive structure") False = undefined
-- typeP_count_pot (JST0P_Function _ _ _ _ _) = 1
-- typeP_count_pot (JST0P_Ret t) = typeP_count_pot t
-- typeP_count_pot (JST0P_Object _ mem) = (membersAn_count_pot mem) +1


isSubtype_P :: TypeP -> TypeP -> Bool
isSubtype_P (JST0P_Function o t n tp np) (JST0P_Function o2 t2 n2 tp2 np2) = let
  bo = (o == o2)
  bt = (t == t2)
  btp = (tp == tp2)
  bn = True -- isLess [n] [n2]
  bnp = True -- isLess [n,np2] [np,n2]
  in bo && bt && btp && bn && bnp
isSubtype_P (JST0P_Object a1 mem1) (JST0P_Object a2 mem2) = let
  (m1,m2) = equalize_alpha (JST0P_Object a1 mem1) (JST0P_Object a2 mem2)
  in isSubtype_Members m1 m2
isSubtype_P a b | a==b = True

isSubtype_An :: TypeAn -> TypeAn -> Bool
isSubtype_An (t1,_nu1,_n1) (t2,_nu2,_n2) = isSubtype_P t1 t2

isSubtype_FieldType :: FieldType -> FieldType -> Bool
isSubtype_FieldType Definite Potential = True
isSubtype_FieldType Potential Potential = True
isSubtype_FieldType Definite Definite = True
isSubtype_FieldType Potential Definite = False

isSubtype_Member :: (TypeAn,FieldType) -> (TypeAn,FieldType) -> Bool
isSubtype_Member (t1,f1) (t2,f2) = (isSubtype_An t1 t2)

isSubtype_Members :: MembersAn -> MembersAn -> Bool
isSubtype_Members mem1 mem2 = Map.foldrWithKey
                              (\k t b -> b &&
                                         (membersAn_contains mem1 k) &&
                                         (isSubtype_Member (membersAn_get mem1 k) t))
                              True
                              mem2

----------------------------------------
-- makes all the annotations in the type distinct, using only annotations with index bigger than the 2nd argument
-- returns: - the distinctified type
--          - the next index to be used
--          - the map of distingtified annotations to originals
----------------------------------------
distingtify_An :: (TypeAn, Int, Map Int Int) -> (TypeAn, Int, Map Int Int)
distingtify_An ((t,nu,n),i,ma) = let (nup,i1,ma1) = distingtify_Annotation (nu,i ,ma )
                                     (np ,i2,ma2) = distingtify_Annotation (n, i1,ma1)
                                     (tp ,i3,ma3) = distingtify_P          (t, i2,ma2)
                                  in ((tp,nup,np),i3,ma3)

distingtify_list :: ([TypeAn],Int,Map Int Int) -> ([TypeAn], Int,Map Int Int)
distingtify_list ([],i,ma) = ([],i,ma)
distingtify_list ((x:xs),i,ma) = 
  let
    (xdis,i2,ma2) = distingtify_An (x,i,ma)
    (xsdis,i3,ma3) = distingtify_list (xs,i2,ma2)
  in (xdis:xsdis,i3,ma3)

distingtify_Annotation :: (Annotation, Int , Map Int Int) -> (Annotation, Int, Map Int Int)
distingtify_Annotation (I k,i,ma) = (I k,i,ma)
distingtify_Annotation (N k,i,ma) = (N i,i+1,Map.insert i k ma)

distingtify_P :: (TypeP, Int, Map Int Int) -> (TypeP, Int, Map Int Int)
distingtify_P (JST0P_Object a mem,i,ma) = let (mem1,i1,ma1) = distingtify_members (mem,i,ma)
                                          in (JST0P_Object a mem1,i1,ma1) 
distingtify_P (JST0P_Function o xs n rs np,i,ma) = 
  let
    (odis ,i1,ma1) = distingtify_An (o,i,ma)
    (xsdis,i2,ma2) = distingtify_list (xs,i1,ma1)
    (ndis, i3,ma3) = distingtify_Annotation (n,i2,ma2)
    (rsdis,i4,ma4) = distingtify_An (rs,i3,ma3)
    (npdis,i5,ma5) = distingtify_Annotation (np,i4,ma4)
  in (JST0P_Function odis xsdis ndis rsdis npdis,i5,ma5)
distingtify_P (t,i,ma) = (t,i,ma) -- simple structures do not get changed

distingtify_member :: ((TypeAn,FieldType),Int , Map Int Int) -> ((TypeAn,FieldType),Int,Map Int Int)
distingtify_member ((t,ft),i,ma) = let (tp,i1,ma1) = distingtify_An (t,i,ma)
                                   in ((tp,ft),i1,ma1)

distingtify_members :: (MembersAn,Int,Map Int Int) -> (MembersAn,Int,Map Int Int)
distingtify_members (mem,i,ma) = Map.foldrWithKey 
                                  (\k t (mem1,i1,ma1) -> let (t2,i2,ma2) = distingtify_member (t,i1,ma1)
                                                         in (Map.insert k t2 mem1,i2,ma2))
                                  (Map.empty,i,ma)
                                  mem

----------------------------------------
-- undoes a distingtification by reverting all annotations according to the map
-- returns - The undistinctified type
----------------------------------------
undistingtify_An :: TypeAn -> Map Int Int -> TypeAn
undistingtify_An n ma | trace 30 ("undistingtify " ++ show n ++ show ma) False = undefined
undistingtify_An (t,nu,n) ma = (undistingtify_P t ma,undistingtify_Annotation nu ma,undistingtify_Annotation n ma)

undistingtify_Annotation :: Annotation -> Map Int Int -> Annotation
undistingtify_Annotation n ma | trace 30 ("undistingtify " ++ show n ++ show ma) False = undefined
undistingtify_Annotation (I k) ma = (I k)
undistingtify_Annotation (N k) ma = let (Just kn) = Map.lookup k ma
                                    in (N kn) 

undistingtify_Annotations :: [Annotation] -> Map Int Int -> [Annotation]
undistingtify_Annotations ns ma | trace 30 ("undistingtify " ++ show ns ++ show ma) False = undefined
undistingtify_Annotations ns ma = Prelude.map (\n -> undistingtify_Annotation n ma) ns

undistingtify_P :: TypeP -> Map Int Int -> TypeP
undistingtify_P n ma | trace 30 ("undistingtify " ++ show n ++ show ma) False = undefined
undistingtify_P (JST0P_Object a mem) ma = (JST0P_Object a (undistingtify_members mem ma))
undistingtify_P t ma = t

undistingtify_member :: (TypeAn,FieldType) -> Map Int Int -> (TypeAn,FieldType)
undistingtify_member n ma | trace 30 ("undistingtify " ++ show n ++ show ma) False = undefined
undistingtify_member (t,tf) ma = (undistingtify_An t ma,tf)

undistingtify_members :: MembersAn -> Map Int Int -> MembersAn
undistingtify_members n ma | trace 30 ("undistingtify " ++ show n ++ show ma) False = undefined
undistingtify_members mem ma = Map.map
                               (\t -> undistingtify_member t ma) mem



----------------------------------------
-- check if an annotated type is None
----------------------------------------
is_none :: TypeAn -> Bool
is_none (JST0P_None,_,_) = True
is_none _ = False