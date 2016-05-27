module JST0_type_aux (
  Path,
  FieldType(Definite,Potential),
  Recu_Variable(..),
  get_gamma
  )
       where

data FieldType = Potential
               | Definite
               deriving Eq

instance Show FieldType where
  show Definite = "⚫"
  show Potential = "⚪"

data Recu_Variable = Alpha Int
                   | Beta Int
                     -- Beta i is only used as the recursive variable in the type for type variable i
                   | Gamma Int -- just used in comparisons
                   | NotRec
                   deriving Eq

instance Show Recu_Variable where
  show (Alpha a) = "α_" ++ (show a)
  show (Beta a) = "β_" ++ (show a)
  show (Gamma a) = "γ_" ++ (show a)
  show (NotRec) = ""

type Path = [String]

rec_var_get_index :: Recu_Variable -> Int
rec_var_get_index (Alpha a) = a
rec_var_get_index (Beta  a) = a
rec_var_get_index (Gamma a) = a

get_gamma :: Recu_Variable -> Recu_Variable
get_gamma (NotRec) = (NotRec)
get_gamma alpha = Gamma (rec_var_get_index alpha)
