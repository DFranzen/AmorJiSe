module Conditionals (
  is_Tnull_JS,
  is_Tint_JS,
  is_TstringLit_JS,
  is_TboolLit_JS,
  is_TobjLit_JS,

  is_TvarR_JS,
  is_TvarW_JS,

  is_TmemR_JS,
  is_TmemW1_JS,
  is_TmemW2_JS,
  is_TmemX_JS,

  is_TfunX_JS,
  is_TnewX_JS,

  is_funExpr_JS,
  is_funExpr,

  is_TvarD_JS,
  is_Tcond_JS,
  is_Twhile_JS,
  is_Tfor_JS,
  is_Treturn_JS,
  is_funStmt_JS,

  is_SourceElementsTop_JS,
  is_Expression_JS,
  is_Variables_JS,
  is_Block_JS,
  is_ExpressionParen_JS,

  is_Statement_single,
  is_Expression_single_JS,
  is_ExpressionParen_single_JS,

  is_OPPlus_JS,
  is_OPArithmetic_JS,
  is_OPComparison_JS,
  is_OPLogic_JS,
  is_OPBang_JS,
  is_OPCond_JS,
  is_OPSign_JS,
  is_OPIntPostfix_JS,
  
  is_irrellevant_JS,
  is_irrellevant_list,
  is_emptyLiteral_JS,
  is_semicolon_JS,

  is_else_JS,

  filter_irrelevant,
  split_assignment,
  split_comma,
  split_semicolon,
  split_arguments,
  split_array,
  split_sequence,
  split_expsequence,
  split_variables,
  head_tail,
) where

import Language.JavaScript.Parser.AST

import Debugging

----------------------------------------
-- conditionals for the typing rules (public API)
----------------------------------------

is_Tnull_JS :: [JSNode] -> Bool
is_Tnull_JS [j] = check_JSNode is_null j
is_Tnull_JS _ = False

is_Tint_JS :: [JSNode] -> Bool
is_Tint_JS [j] = check_JSNode is_int j
is_Tint_JS _ = False

is_TobjLit_JS :: [JSNode] -> Bool
is_TobjLit_JS [j] = is_objDecl_JS j
is_TobjLit_JS _ = False

is_TstringLit_JS :: [JSNode] -> Bool
is_TstringLit_JS [j] = (check_JSNode is_string) j
is_TstringLit_JS _ = False

is_TboolLit_JS :: [JSNode] -> Bool
is_TboolLit_JS [j] = (check_JSNode is_boollit) j
is_TboolLit_JS _ = False

is_TvarR_JS :: [JSNode] -> Bool
is_TvarR_JS [j] = is_var_acc_JS j
is_TvarR_JS _ = False

is_TvarW_JS :: [JSNode] -> Bool
is_TvarW_JS js | is_assignment_JS js = let
  (l,o,r) = split_assignment js
  in is_var_acc_list l
is_TvarW_JS _ = False

is_TmemR_JS :: [JSNode] -> Bool
is_TmemR_JS = is_obj_lu_JS

is_TmemW1_JS :: [JSNode] -> Bool
is_TmemW1_JS js | is_assignment_JS js = let
             (l,o,r) = split_assignment js
             in is_field_of_var_JS l
is_TmemW1_JS _ = False

is_TmemW2_JS :: [JSNode] -> Bool
is_TmemW2_JS js | is_assignment_JS js = let
             (l,o,r) = split_assignment js
             in (not (is_field_of_var_JS l)) && is_obj_lu_JS l
is_TmemW2_JS _ = False

is_TmemX_JS :: [JSNode] -> Bool
is_TmemX_JS = is_object_call_JS

is_TfunX_JS :: [JSNode] -> Bool
is_TfunX_JS = is_function_call_JS

is_TnewX_JS :: [JSNode] -> Bool
is_TnewX_JS = is_new_call_JS

-- Statements

is_Tcond_JS :: JSNode -> Bool
is_Tcond_JS = is_if_JS

is_TvarD_JS :: JSNode -> Bool
is_TvarD_JS = is_VarDecl_JS

is_Twhile_JS :: JSNode -> Bool
is_Twhile_JS = check_JSNode is_while

is_Tfor_JS :: JSNode -> Bool
is_Tfor_JS = check_JSNode is_for

is_Treturn_JS :: JSNode -> Bool
is_Treturn_JS = check_JSNode is_return

is_Block_JS :: JSNode -> Bool
is_Block_JS = check_JSNode is_block

is_SourceElementsTop_JS :: JSNode -> Bool
is_SourceElementsTop_JS = check_JSNode is_sourceelementstop

is_Expression_JS :: JSNode -> Bool
is_Expression_JS = check_JSNode is_expression

is_Expression_single_JS :: [JSNode] -> Bool
is_Expression_single_JS [j] = is_Expression_JS j
is_Expression_single_JS _ = False

is_ExpressionParen_single_JS :: [JSNode] -> Bool
is_ExpressionParen_single_JS [j] = is_ExpressionParen_JS j
is_ExpressionParen_single_JS _ = False

is_Statement_single :: [JSNode] -> Bool
is_Statement_single [j] = is_Expression_JS j || is_Variables_JS j || is_Block_JS j || is_ExpressionParen_JS j
is_Statement_single _ = False

is_Variables_JS :: JSNode -> Bool
is_Variables_JS = check_JSNode is_variables

is_ExpressionParen_JS :: JSNode -> Bool
is_ExpressionParen_JS = check_JSNode is_expressionparen

-- operators

is_OPPlus_JS :: [JSNode] -> Bool
is_OPPlus_JS [j] = (check_JSNode is_plusop) j
is_OPPlus_JS _ = False

is_OPArithmetic_JS :: [JSNode] -> Bool
is_OPArithmetic_JS [j] = (check_JSNode is_intop) j
is_OPArithmetic_JS _ = False

is_OPComparison_JS :: [JSNode] -> Bool
is_OPComparison_JS [j] = (check_JSNode is_boolresop) j
is_OPComparison_JS _ = False

is_OPLogic_JS :: [JSNode] -> Bool
is_OPLogic_JS [j] = (check_JSNode is_boolop) j
is_OPLogic_JS _ = False

is_OPBang_JS :: [JSNode] -> Bool
is_OPBang_JS js | trace 30 ("OP!Check" ++ show js) False = undefined
is_OPBang_JS (j:js) = (check_JSNode is_bangop) j
is_OPBang_JS _ = False

is_OPCond_JS :: [JSNode] -> Bool
is_OPCond_JS [j] = (check_JSNode is_condop) j
is_OPCond_JS _ = False

is_OPSign_JS :: [JSNode] -> Bool
is_OPSign_JS js | trace 30 ("OP-Check" ++ show js) False = undefined
is_OPSign_JS (j:js) = (check_JSNode is_signop) j
is_OPSign_JS _ = False

is_OPIntPostfix_JS :: [JSNode] -> Bool
is_OPIntPostfix_JS [j] = (check_JSNode is_intPostfixop) j
is_OPIntPostfix_JS _ = False

----------------------------------------
-- Backbone checks
----------------------------------------

----------------------------------------
-- Basic Value Literals
----------------------------------------

is_null :: Node -> Bool
is_null (JSLiteral s) = (s == "null")
is_null _ = False

is_int :: Node -> Bool
is_int (JSDecimal _i) = True
is_int _other = False

is_string :: Node -> Bool
is_string (JSStringLiteral _delim _s ) = True
is_string _other = False

is_boollit :: Node -> Bool
is_boollit (JSLiteral "false") = True
is_boollit (JSLiteral "true") = True
is_boollit _ = False

is_objDecl :: Node -> Bool
is_objDecl (JSObjectLiteral _lb _fields _rb) = True
is_objDecl _ = False

is_objDecl_JS :: JSNode -> Bool
is_objDecl_JS = check_JSNode is_objDecl

----------------------------------------
-- Checking a list against a list of conditionals
----------------------------------------

check_JSNode :: (Node -> Bool) -> JSNode -> Bool
check_JSNode f (NN n) = f n
check_JSNode f (NT n _ _) = check_JSNode f (NN n)

check_JSNodes_head :: [JSNode -> Bool] -> [JSNode] -> Bool
check_JSNodes_head [] _ = True
check_JSNodes_head (b:bs) (j:js) = (b j) && check_JSNodes_head bs js
check_JSNodes_head _ [] = False

is_JSNode :: JSNode -> Bool
is_JSNode _ = True

----------------------------------------
-- Check if the Node is irrelevant for the analysis
----------------------------------------

is_irrellevant :: Node -> Bool
is_irrellevant (JSLiteral "") = True
--is_irrellevant (JSLiteral ";") = True
--is_irrellevant (JSLiteral ",") = True
is_irrellevant (JSLiteral "else") = True
is_irrellevant _ = False

is_irrellevant_JS :: JSNode -> Bool
is_irrellevant_JS = check_JSNode is_irrellevant

is_irrellevant_list :: [JSNode] -> Bool
is_irrellevant_list [] = True
is_irrellevant_list (x:xs) = (is_irrellevant_JS x) && (is_irrellevant_list xs)

is_emptyLiteral :: Node -> Bool
is_emptyLiteral (JSLiteral "") = True
is_emptyLiteral _ = False

is_emptyLiteral_JS :: JSNode -> Bool
is_emptyLiteral_JS = check_JSNode is_emptyLiteral

is_emptyStatement :: Node -> Bool
is_emptyStatement j = is_emptyLiteral j || is_semicolon j

is_emptyStatement_JS :: JSNode -> Bool
is_emptyStatement_JS = check_JSNode is_emptyStatement

filter_irrelevant :: [JSNode] -> [JSNode]
filter_irrelevant js = Prelude.filter (\j -> not (is_irrellevant_JS j)) js

----------------------------------------
-- Tests for simple constructs
----------------------------------------

is_while :: Node -> Bool
is_while (JSWhile _while _rb _bool _lb _e) = True
is_while _ = False

is_for :: Node -> Bool
is_for (JSFor _for _rb [_e1] _sem1 [_e2] _sem2 [_e3] _lb _body) = True
is_for (JSForVar _for _rb _var _e1 _sem1 [_e2] _sem2 [_e3] _lb _body) = True
is_for _ = False

is_return :: Node -> Bool
is_return (JSReturn _lit _e _lim) = True
is_return _ = False


is_if :: Node -> Bool
is_if (JSIf _if _lb _bool _rb _true _cont) = True
is_if _ = False

is_if_JS :: JSNode -> Bool
is_if_JS = check_JSNode is_if

is_else :: Node -> Bool
is_else (JSLiteral "else") = True
is_else _ = False

is_else_JS :: JSNode -> Bool
is_else_JS = check_JSNode is_if

is_VarDecl :: Node -> Bool 
is_VarDecl (JSVarDecl _x _decl) = True
is_VarDecl _ = False

is_VarDecl_JS :: JSNode -> Bool
is_VarDecl_JS = check_JSNode is_VarDecl

-- variable access
is_var_acc :: Node -> Bool
is_var_acc (JSIdentifier _x) = True
is_var_acc (JSLiteral "this") = True
is_var_acc _ = False

is_var_acc_JS :: JSNode -> Bool
is_var_acc_JS = check_JSNode is_var_acc

is_var_acc_list :: [JSNode] -> Bool
is_var_acc_list [j] = is_var_acc_JS j
is_var_acc_list _ = False

-- assignments

is_assignment_JS :: [JSNode] -> Bool
is_assignment_JS js = (not (is_sequence_JS js)) && (is_assignment_test js)

is_assignment_test :: [JSNode] -> Bool
is_assignment_test [] = False
is_assignment_test (j:js) = (is_equal_JS j) || (is_assign_op_JS j) || (is_assignment_test js)

-- expression sequence
is_sequence_JS :: [JSNode] -> Bool
is_sequence_JS [] = False
is_sequence_JS (j:js) = (is_comma_JS j) || (is_sequence_JS js)

----------------------------------------
-- Source Boxes
----------------------------------------
is_expression :: Node -> Bool
is_expression (JSExpression _js) = True
is_expression _ = False

is_block :: Node -> Bool
is_block (JSBlock _rb _js _lb) = True
is_block _ = False

is_expressionparen :: Node -> Bool
is_expressionparen (JSExpressionParen _rb _j _lb) = True
is_expressionparen _ = False

is_sourceelementstop :: Node -> Bool
is_sourceelementstop (JSSourceElementsTop _js) = True
is_sourceelementstop _ = False

is_variables :: Node -> Bool
is_variables (JSVariables _var _js _cont) = True
is_variables _ = False

----------------------------------------
-- Tests for operators
----------------------------------------

is_boolresop :: Node -> Bool
is_boolresop (JSExpressionBinary "==" _e1 _op _e2) = True
is_boolresop (JSExpressionBinary "===" _e1 _op _e2) = True
is_boolresop (JSExpressionBinary "!==" _e1 _op _e2) = True
is_boolresop (JSExpressionBinary "!=" _e1 _op _e2) = True
is_boolresop (JSExpressionBinary "<" _e1 _op _e2) = True
is_boolresop (JSExpressionBinary ">" _e1 _op _e2) = True
is_boolresop (JSExpressionBinary ">=" _e1 _op _e2) = True
is_boolresop (JSExpressionBinary "<=" _e1 _op _e2) = True
is_boolresop _ = False

is_boolop :: Node -> Bool
is_boolop (JSExpressionBinary "||" _e1 _op _e2) = True
is_boolop (JSExpressionBinary "&&" _e1 _op _e2) = True
is_boolop _ = False

is_intPostfixop :: Node -> Bool
is_intPostfixop (JSExpressionPostfix "++" _js _op) = True
is_intPostfixop (JSExpressionPostfix "--" _js _op) = True
is_intPostfixop _ = False

is_plusop :: Node -> Bool
is_plusop (JSExpressionBinary "+" _e1 _op _e2) = True
is_plusop _ = False

is_intop :: Node -> Bool
is_intop (JSExpressionBinary "-" _e1 _op _e2) = True
is_intop (JSExpressionBinary "*" _e1 _op _e2) = True
is_intop (JSExpressionBinary "/" _e1 _op _e2) = True
is_intop (JSExpressionBinary "%" _e1 _op _e2) = True
is_intop _ = False

is_bangop :: Node -> Bool
is_bangop (JSUnary "!" _l) = True
is_bangop _ = False

is_signop :: Node -> Bool
is_signop (JSUnary "-" _l) = True
is_signop (JSUnary "+" _l) = True
is_signop _ = False

is_condop :: Node -> Bool
is_condop (JSExpressionTernary _cond _qm _t _colon _f) = True
is_condop _ = False

is_assign_op :: Node -> Bool
is_assign_op (JSOperator o) = is_equal_JS o
is_assign_op _ = False

is_assign_op_JS :: JSNode -> Bool
is_assign_op_JS = check_JSNode is_assign_op

is_equal :: Node -> Bool
is_equal (JSLiteral "=") = True
is_equal _ = False

is_equal_JS :: JSNode -> Bool
is_equal_JS = check_JSNode is_equal

is_comma :: Node -> Bool
is_comma (JSLiteral ",") = True
is_comma _ = False 

is_comma_JS :: JSNode -> Bool
is_comma_JS = check_JSNode is_comma

is_semicolon :: Node -> Bool
is_semicolon (JSLiteral ";") = True
is_semicolon _ = False 

is_semicolon_JS :: JSNode -> Bool
is_semicolon_JS = check_JSNode is_semicolon

is_elision :: Node -> Bool
is_elision (JSElision _) = True
is_elision _ = False

is_elision_JS :: JSNode -> Bool
is_elision_JS = check_JSNode is_elision

----------------------------------------
-- Tests for function 
----------------------------------------

-- Decl
is_funDecl :: Node -> Bool
is_funDecl n = (is_funStmt n) || (is_funExpr n)

is_funStmt :: Node -> Bool
is_funStmt (JSFunction _function _f _lb _args _rb _e) = True
is_funStmt _ = False

is_funExpr :: Node -> Bool
is_funExpr (JSFunctionExpression _function _f _lb _args _rb _e) = True
is_funExpr _ = False

is_funDecl_JS :: JSNode -> Bool
is_funDecl_JS = check_JSNode is_funDecl

is_funExpr_JS :: [JSNode] -> Bool
is_funExpr_JS [j] = check_JSNode is_funExpr j
is_funExpr_JS _ = False

is_funStmt_JS :: JSNode -> Bool
is_funStmt_JS = check_JSNode is_funStmt

-- Call
--   type
is_new :: Node -> Bool
is_new (JSLiteral "new") = True
is_new _ = False

is_new_JS :: JSNode -> Bool
is_new_JS = check_JSNode is_new

is_new_call_JS :: [JSNode] -> Bool
is_new_call_JS [] = False
is_new_call_JS [j] = False
is_new_call_JS (j:js) = is_new_JS j 

is_object_call_JS :: [JSNode] -> Bool
is_object_call_JS [] = False
is_object_call_JS [j] = False
is_object_call_JS js = let
                  (h,t) = head_tail js
                  in (not (is_new_call_JS h)) && 
                     (is_obj_lu_JS h) && 
                     (is_argument_JS t)
              
is_function_call_JS :: [JSNode] -> Bool
is_function_call_JS [] = False
is_function_call_JS [j] = False
is_function_call_JS (j:js) = let
                    (h,t) = head_tail js
                    in (not (is_new_call_JS h)) &&
                       (not (is_obj_lu_JS h)) &&
                       (is_argument_JS t)

--   arguments
is_argument_last :: [JSNode] -> Bool
is_argument_last [] = False
is_argument_last [j] = is_argument_JS j
is_argument_last (j:js) = is_argument_last js

is_argument :: Node -> Bool
is_argument (JSArguments _ _ _) = True
is_argument (JSCallExpression "()" [] [NN (JSArguments _ _ _)] []) = True
is_argument _ = False

is_argument_JS :: JSNode -> Bool
is_argument_JS = check_JSNode is_argument

head_tail :: [a] ->  ([a],a)
head_tail [] | error ("Access to last element of empty list") = undefined
head_tail [j] = ([],j)
head_tail (j:js) = let
          (h,t) = head_tail js
          in (j:h,t)

----------------------------------------
-- Conditionals for Object access
----------------------------------------

-- simple field access to variable
is_field_of_var :: Node -> Bool
is_field_of_var (JSMemberDot [o] _p _field) = is_var_acc_JS o
is_field_of_var (JSMemberSquare [o] _bl _field _br) = is_var_acc_JS o
is_field_of_var _ = False

is_field_of_var_JS :: [JSNode] -> Bool
is_field_of_var_JS [j] = check_JSNode is_field_of_var j
is_field_of_var_JS _ = False


-- access to an member of the preceeding object
is_mem_acc :: Node -> Bool
is_mem_acc (JSCallExpression "." _ mem []) = True
is_mem_acc (JSCallExpression "[]" _ mem _) = True
is_mem_acc _ = False

is_mem_acc_JS :: JSNode -> Bool
is_mem_acc_JS = check_JSNode is_mem_acc

-- direct object access in one JSNode
is_obj_acc :: Node -> Bool
is_obj_acc (JSMemberDot _ _ _) = True
is_obj_acc (JSMemberSquare _ _ _ _) = True
is_obj_acc _ = False

is_obj_acc_JS :: JSNode -> Bool
is_obj_acc_JS = check_JSNode is_obj_acc

-- indirect object lookup in [JSNode]
is_obj_lu_JS ::[JSNode] -> Bool
is_obj_lu_JS [] = False
is_obj_lu_JS [j] = is_obj_acc_JS j
is_obj_lu_JS js = is_obj_lu_last js

is_obj_lu_last :: [JSNode] -> Bool
is_obj_lu_last [] = False
is_obj_lu_last [j] = is_mem_acc_JS j
is_obj_lu_last (j:js) = is_obj_lu_last js

----------------------------------------
-- Code to identify potentially resource consuming code
----------------------------------------

-- is the node sequence a call to cordova.exec?
-- is_cordova_exec_call :: [JSNode] -> Bool
-- is_cordova_exec_call (js1:(js2:_)) = is_cordova_exec_acc_JS js1 && is_argument_JS js2
-- is_cordova_exec_call _ = False

-- --is the node sequence a call to a navigator method?
-- is_navigator_call :: [JSNode] -> Bool
-- is_navigator_call (js1:(js2:_)) = is_navigator_acc_JS js1 && is_argument_JS js2
-- is_navigator_call _ = False

-- -- is the node sequence an access to cordova.exec
-- is_cordova_exec_acc_JS :: JSNode -> Bool
-- is_cordova_exec_acc_JS (NN n) = is_cordova_exec_acc n
-- is_cordova_exec_acc_JS (NT n _ _) = is_cordova_exec_acc n

-- is_cordova_exec_acc :: Node -> Bool
-- is_cordova_exec_acc (JSMemberDot obj _ field) = is_cordova_list obj && is_exec_JS field
-- is_cordova_exec_acc (JSMemberSquare obj _ field _) = is_cordova_list obj && is_exec_JS field
-- is_cordova_exec_acc _ = False

-- -- is the node sequence an access to navigator
-- is_navigator_acc_list :: [JSNode] -> Bool
-- is_navigator_acc_list [x] = is_navigator_acc_JS x
-- is_navigator_acc_list (_:xs) = is_navigator_acc_list xs
-- is_navigator_acc_list _ = False

-- is_navigator_acc_JS :: JSNode -> Bool
-- is_navigator_acc_JS (NN n) = is_navigator_acc n
-- is_navigator_acc_JS (NT n _ _) = is_navigator_acc n

-- is_navigator_acc :: Node -> Bool
-- is_navigator_acc (JSMemberDot objs _sep _field) = is_navigator_acc_list objs
-- is_navigator_acc (JSMemberSquare objs _lb _field _rb) = is_navigator_acc_list objs
-- is_navigator_acc (JSIdentifier s) = s == "navigator"
-- is_navigator_acc _ = False

-- is--  the node access to the exec identifier
-- is_exec_JS :: JSNode -> Bool
-- is_exec_JS (NT n _ _) = is_exec n
-- is_exec_JS (NN n) = is_exec n

-- is_exec :: Node -> Bool
-- is_exec (JSIdentifier s) = s == "exec"
-- is_exec (JSExpression ss) = is_exec_list ss

-- is_exec_list :: [JSNode] -> Bool
-- is_exec_list [] = False
-- is_exec_list (x:_) = is_exec_JS x

-- -- is the node sequence access the cordova object
-- is_cordova_list :: [JSNode] -> Bool
-- is_cordova_list = is_list_single is_cordova

-- is_cordova :: Node -> Bool
-- is_cordova (JSIdentifier s) = s == "cordova"
-- is_cordova _ = False

-- -- is the node sequence access the navigator object
-- is_navigator_list :: [JSNode] -> Bool
-- is_navigator_list = is_list_single is_navigator 

-- is_navigator :: Node -> Bool
-- is_navigator (JSIdentifier s) = s == "navigator"
-- is_navigator _n = False

-- Auxiliary functions

--is_list_single :: (Node -> Bool) -> [JSNode] -> Bool
--is_list_single f l | is_single_JSNode l = let
--  n = get_single_JSNode l
--  in f n
--                   | otherwise = False

-- get_single_JSNode :: [JSNode] -> Node
-- get_single_JSNode [NN n] = n
-- get_single_JSNode [NT n _p _cs] = n

-- is_single_JSNode:: [JSNode] -> Bool
-- is_single_JSNode [_js] = True
-- is_single_JSNode _jss = False


----------------------------------------
-- Split into subexpressions
----------------------------------------

-- left-to-right: Split of the left most expression and leave the rest together
split_comma :: [JSNode] -> ([JSNode], [JSNode])
split_comma [] = ([],[])
split_comma (j:js) | is_comma_JS j = ([],js)
                   | otherwise = let
                   (h,t) = split_comma js
                   hn | is_irrellevant_JS j = h
                      | otherwise = (j:h)
                   in (hn,t)

split_semicolon :: [JSNode] -> (JSNode,[JSNode])
split_semicolon [] = (NN (JSLiteral ""),[])
split_semicolon (j:js) | is_semicolon_JS j = (NN (JSLiteral ""),js)
                       | otherwise = let
                       (NN (JSLiteral ""),t) = split_semicolon js
                       in (j,t)

split_elision :: [JSNode] -> ([JSNode],[JSNode])
split_elision [] = ([],[])
split_elision (j:js) | is_elision_JS j = ([],js)
                     | otherwise = let
                     (h,t) = split_elision js
                     in (j:h,t)

-- right to left. Every comma is interpretted as seperator
split_arguments :: [JSNode] -> [[JSNode]]
split_arguments [] = []
split_arguments js = let
                (first,rest) = split_comma js
                rest_split = split_arguments rest
                in first:rest_split

-- right-to-left: Split of the right most expression, also return the operator
-- return (lhs,op,rhs)
split_assignment :: [JSNode] -> ([JSNode],[JSNode],[JSNode])
split_assignment js | trace 30 ("split_assignment " ++ show js) False = undefined
split_assignment [] = ([],[],[])
split_assignment (j:js) = let
  (l,o,r) = split_assignment js
  (ln,on,rn) | (o == []) && (is_equal_JS j)     = ([],[j],r)
             | (o == []) && (is_assign_op_JS j) = ([],[j,NN (JSLiteral " ")],r)
             | (o == [])                        = ([],[],j:r)
             | otherwise                        = (j:l,o,r)
  in (ln,on,rn)

split_array :: [JSNode] -> [[JSNode]]
split_array [] = []
split_array js = let
            (first,rest) = split_elision js
            rest_split = split_array rest
            in first:rest_split

split_sequence :: [JSNode] -> [JSNode]
split_sequence [] = []
split_sequence (j:js) | is_semicolon_JS j = split_sequence js
                      | is_emptyLiteral_JS j = split_sequence js
                      | otherwise    =  j : split_sequence js

split_expsequence :: [JSNode] -> [[JSNode]]
split_expsequence [] = []
split_expsequence js = let 
                  (first,rest) = split_comma js
                  rest_split = split_expsequence rest
                  in first:rest_split

split_variables :: [JSNode] -> [JSNode]
split_variables [] = []
split_variables (j:js) | is_comma_JS j = split_variables js
                       | otherwise = j : split_variables js

