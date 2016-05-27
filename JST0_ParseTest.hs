module Main where

import Language.JavaScript.Parser.Parser
import Language.JavaScript.Parser.AST

import Conditionals
import Extraction
import Debugging

import Data.MultiSet as MultiSet

type Missing = MultiSet String
type PT_OUT = (Bool,Int,Int,Missing)



main:: IO()
main = do 
     fname <- getLine
     fcont <- readFile fname
     putStr (fname ++ "," ++ (pt_csv fname fcont) ++"\n")

pt_one :: String -> IO()
pt_one fname = do
       fcont <- readFile fname
       putStr (pt_verbose fname fcont)
       
pt_csv :: String -> String -> String
pt_csv fname fcont = let
       (success,fun,funsucc,com) = pt_string fname fcont
       in show success ++ "," ++ 
          show fun ++ "," ++ 
          show funsucc ++ "," ++ 
          show (show com) ++ "," ++
          show (MultiSet.distinctSize com) ++ ";" 
pt_verbose :: String -> String -> String
pt_verbose fname fcont = let
    (success,fun,funsucc,com) = pt_string fname fcont
    res | success =
      "Success: " ++ fname ++ "\nFunctions parsed: (" ++ show fun ++ "/" ++ show funsucc ++ ")"
        | otherwise = "Fail: \n Functions parsed: (" ++ show fun ++ "/" ++ show funsucc ++ ")"
        in res ++ "\nComments: " ++ (show com) ++ "\n"


pt_string :: String -> String -> PT_OUT
pt_string f_name s = pt_parsed f_name (parse s f_name)

pt_parsed :: String -> Either String JSNode -> PT_OUT
pt_parsed file_name (Left s) | error ("Parser Error: " ++ file_name ++ "\n" ++ s) = undefined
pt_parsed file_name (Right a) = pt_Statement a
  
pt_Statement :: JSNode -> PT_OUT
pt_Statement (NT n _ _ ) = pt_Statement (NN n)
pt_Statement js
  | is_SourceElementsTop_JS js = pt_EnS js
  | is_Expression_JS js        = pt_EnS js
  | is_Variables_JS js         = pt_EnS js
  | is_Block_JS js             = pt_EnS js
  | is_ExpressionParen_JS js   = pt_EnS js

  -- unneccessary
  | is_emptyLiteral_JS js = (True,0,0,MultiSet.empty)
  | is_semicolon_JS js = (True,0,0,MultiSet.empty)

  -- statements
  | is_TvarD_JS js   = pt_EnS js
  | is_Tcond_JS js   = pt_cond (ex_Tcond js)
  | is_Twhile_JS js  = pt_Twhile (ex_Twhile js)
  | is_Tfor_JS    js = pt_Tfor   (ex_Tfor   js)
  | is_Treturn_JS js = pt_EnS js

  | is_funStmt_JS js = pt_fun (ex_TfunStmt js)
  | otherwise = let
    (_success,fun,funsucc,com) = pt_EnS js
    in (False,fun,funsucc,MultiSet.insert (ex_JSId js)com)

pt_Statement_mult :: [JSNode] -> PT_OUT
pt_Statement_mult [] = (True,0,0,MultiSet.empty)
pt_Statement_mult (j:js) = add (pt_Statement j) (pt_Statement_mult js)

pt_EnS :: JSNode -> PT_OUT
pt_EnS js = let
       js_e = ex_Expressions js
       js_s = ex_Statements js
       in add (pt_Expression_mult js_e) (pt_Statement_mult js_s)

pt_EnS_mult :: [JSNode] -> PT_OUT
pt_EnS_mult [] = (True,0,0,MultiSet.empty)
pt_EnS_mult (j:js) = add (pt_EnS j) (pt_EnS_mult js)

pt_Expression :: [JSNode] -> PT_OUT
pt_Expression js | trace 30 ("\n-->Expression" ++ show js) False = undefined
pt_Expression js_dirty = let
  js = filter_irrelevant js_dirty
  res 
    | is_Expression_single_JS js      = pt_Expression_mult (ex_Expression_single      js)
    | is_ExpressionParen_single_JS js = pt_Expression_mult (ex_ExpressionParen_single js)

    | is_Tnull_JS js      = (True,0,0,MultiSet.empty)
    | is_Tint_JS js       = (True,0,0,MultiSet.empty)
    | is_TboolLit_JS js   = (True,0,0,MultiSet.empty)
    | is_TstringLit_JS js = (True,0,0,MultiSet.empty)
    | is_TobjLit_JS js    = pt_fields (ex_TobjLit js)


    | is_TvarR_JS js  = pt_EnS_mult js
    | is_TvarW_JS js  = pt_varW (ex_TvarW js)
    | is_TmemR_JS js  = pt_EnS_mult js
    | is_TmemW1_JS js = pt_memW1 (ex_TmemW1 js)
    | is_TmemW2_JS js = pt_memW2 (ex_TmemW2 js)
    | is_TnewX_JS js  = pt_newX (ex_TnewX js)
    | is_TmemX_JS js  = pt_memX (ex_TmemX js)
    | is_TfunX_JS js  = pt_funX (ex_TfunX js)

    | is_funExpr_JS js = pt_fun (ex_TfunExpr js)

    | is_OPPlus_JS       js = pt_OPBin (ex_BinOp js)
    | is_OPArithmetic_JS js = pt_OPBin (ex_BinOp js)
    | is_OPComparison_JS js = pt_OPBin (ex_BinOp js)
    | is_OPLogic_JS      js = pt_OPBin (ex_BinOp js)
    | is_OPBang_JS       js = pt_OPUn  (ex_UnOp  js)
    | is_OPSign_JS       js = pt_OPUn  (ex_UnOp  js)
    | is_OPCond_JS       js = pt_OPTer (ex_TerOp js)
    | is_OPIntPostfix_JS js = pt_OPPF  (ex_PostfixOp js)

    | js == [] = (True,0,0,MultiSet.empty)
    | otherwise = let
      (_s,f,fs,c) = pt_Statement_mult js
      in (False,f,fs,c)

  in res

pt_Expression_mult :: [[JSNode]] -> PT_OUT
pt_Expression_mult [] = (True,0,0,MultiSet.empty)
pt_Expression_mult (j:js) = add (pt_Expression j) (pt_Expression_mult js)

add :: PT_OUT -> PT_OUT -> PT_OUT
add (succj,funj,funsuccj,comj) (succjs,funjs,funsuccjs,comjs) =
    (succj && succjs,funj + funjs,funsuccj + funsuccjs,MultiSet.union comj comjs)

pt_fields :: [(String,[JSNode])] -> PT_OUT
pt_fields [] = (True,0,0,MultiSet.empty)
pt_fields ((s,js):jx) = add (pt_Expression js) (pt_fields jx)

pt_fun :: (String,[String],JSNode) -> PT_OUT
pt_fun (_name,_params,j) = let
       (s,f,fs,c) = pt_Statement j
       fsn | s = fs+1
           | otherwise = fs
       in (s,f+1,fsn,c)

pt_memX :: ([JSNode],String,[[JSNode]]) -> PT_OUT
pt_memX (e1,m,ei) = add (pt_Expression e1) (pt_Expression_mult ei)

pt_funX :: ([JSNode],[[JSNode]]) -> PT_OUT
pt_funX (e1,ei) = add (pt_Expression e1) (pt_Expression_mult ei)

pt_newX :: ([JSNode],[[JSNode]]) -> PT_OUT
pt_newX (e1,ei) = add (pt_Expression e1) (pt_Expression_mult ei)
        
pt_varW :: (String,[JSNode]) -> PT_OUT
pt_varW (s,e) | trace 30 ("pt_varW" ++ s ++ "=" ++ show e) False = undefined
pt_varW (s,e) = pt_Expression e

pt_memW1 :: (String,String,[JSNode]) -> PT_OUT
pt_memW1 (var,m,e) = pt_Expression e

pt_memW2 :: ([JSNode],String,[JSNode]) -> PT_OUT
pt_memW2 (o,m,e) = add (pt_Expression o) (pt_Expression e)

pt_cond :: (JSNode,JSNode,JSNode) -> PT_OUT
pt_cond (b,e1,e2) = pt_Statement_mult [b,e1,e2]

pt_Twhile :: (JSNode,JSNode) -> PT_OUT
pt_Twhile (bool,body) = pt_Statement_mult [bool,body]

pt_Tfor :: ([JSNode],JSNode,JSNode,JSNode) -> PT_OUT
pt_Tfor (e1,e2,e3,body) = pt_Statement_mult (e2:e3:body:e1)

pt_OPBin :: ([JSNode],[JSNode]) -> PT_OUT
pt_OPBin (e1,e2) = pt_Expression_mult [e1,e2]

pt_OPUn :: [JSNode] -> PT_OUT
pt_OPUn e1 = pt_Expression e1

pt_OPTer :: ([[JSNode]],[[JSNode]],[[JSNode]]) -> PT_OUT
pt_OPTer (e1,e2,e3) = pt_Expression_mult (concat [e1,e2,e3])

pt_OPPF :: [JSNode] -> PT_OUT
pt_OPPF e1 = pt_Expression e1


