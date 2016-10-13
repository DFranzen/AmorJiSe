module Res_model where

import JST0P_types
import JST0_type_aux

c_varR :: Annotation
c_varR = I 0

c_varW :: Annotation
c_varW = I 0

c_memR :: Annotation
c_memR = I 0

c_memW :: FieldType -> Annotation
c_memW a = case a of
  Potential -> I 0
  Definite -> I 0

c_new :: Annotation
c_new = I 0

c_funX :: Annotation
c_funX = I 0

c_seq :: Annotation
c_seq = I 0

c_cond :: Annotation
c_cond = I 0

c_varD :: Annotation
c_varD = I c_varDi

c_varDi :: Int
c_varDi = 0

c_funD :: Annotation
c_funD = I c_funDi

c_funDi :: Int
c_funDi = 0

c_objD :: Annotation
c_objD = I 0
--c_int :: Annotation
--c_int = I 1
