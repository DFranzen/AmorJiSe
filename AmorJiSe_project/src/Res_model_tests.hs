module Res_model where

import JST0P_types
import JST0_type_aux



-- Value read
c_val :: Int
c_val = 1

-- Variable read
c_varR :: Int
c_varR = 2

-- Variable Write
c_varW :: Int
c_varW = 4

-- Field (member) read
c_memR :: Int
c_memR = 8

-- Field (member) write
c_memW :: FieldType -> Int
c_memW a = case a of
  Definite -> 16
  Potential -> 32

-- Constructor invocation
c_new :: Int
c_new = 64

-- Function invocation
c_funX :: Int
c_funX = 128

-- Expression concatenation
c_seq :: Int
c_seq = 512

-- Conditional Evaluation
c_cond :: Int 
c_cond = 1024

-- Variable definition
c_varD :: Int
c_varD = c_varDi

-- Variable definition (Integer)
-- used to multiply by for multiple var declarations
c_varDi :: Int
c_varDi = 2048

-- Function definition
c_funD :: Int
c_funD = c_funDi

-- Function definition (Integer)
c_funDi :: Int
c_funDi = 4096

-- Object Definition
c_objD :: Int
c_objD = 8192

--c_int :: Annotation
--c_int = I 1
