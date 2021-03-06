module Res_model where

import JST0P_types
import JST0_type_aux



-- Value read
c_val :: Int
c_val = 0

-- Variable read
c_varR :: Int
c_varR = 0

-- Variable Write
c_varW :: Int
c_varW = 0

-- Field (member) read
c_memR :: Int
c_memR = 0

-- Field (member) write
c_memW :: FieldType -> Int
c_memW a = case a of
  Definite -> 0
  Potential -> 1

-- Constructor invocation
c_new :: Int
c_new = 1

-- Function invocation
c_funX :: Int
c_funX = 0

-- Expression concatenation
c_seq :: Int
c_seq = 0

-- Conditional Evaluation
c_cond :: Int 
c_cond = 0

-- Variable definition
c_varD :: Int
c_varD = c_varDi

-- Variable definition (Integer)
-- used to multiply by for multiple var declarations
c_varDi :: Int
c_varDi = 1

-- Function definition
c_funD :: Int
c_funD = c_funDi

-- Function definition (Integer)
c_funDi :: Int
c_funDi = 1

-- Object Definition
c_objD :: Int
c_objD = 1

--c_int :: Annotation
--c_int = I 1
