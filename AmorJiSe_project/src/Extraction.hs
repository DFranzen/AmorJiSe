module Extraction (
  ex_code,
  ex_code_list,

  ex_TstringLit,
  ex_TobjLit,

  ex_TvarR,
  ex_TvarW,

  ex_TmemR,
  ex_TmemW1,
  ex_TmemW2,
  ex_TmemX,

  ex_TfunX,
  ex_TnewX,

  ex_TfunStmt,
  ex_TfunExpr,

  ex_TvarD,
  ex_Tcond,
  ex_Twhile,
  ex_Tfor,
  ex_Treturn,

  ex_TerOp,
  ex_BinOp,
  ex_UnOp,
  ex_PostfixOp,

  ex_fID,
  ex_JSId,

  showCode,

  ex_Statements,
  ex_Expressions,
  
  ex_SourceElementsTop,
  ex_Expression,
  ex_Variables,
  ex_Block,
  ex_ExpressionParen,

  ex_Expression_single,
  ex_ExpressionParen_single,
  ) where

import Language.JavaScript.Parser.AST

import Conditionals

import Debugging

----------------------------------------
-- Extractions for the rules
----------------------------------------

ex_TvarR :: [JSNode] -> String
ex_TvarR _ | trace 30 "ex_TvarR" False = undefined
ex_TvarR [j] = ex_var_name_JS j
ex_TvarR _ | error "varR not recognized" = undefined
           | otherwise = undefined

ex_TvarW :: [JSNode] -> (String, [JSNode])
ex_TvarW _js | trace 30 ("ex_TvarW ") False = undefined
ex_TvarW js = let
         (l,_o,r) = split_assignment js
         (j:rest) = l
         var_name | (rest == []) = j
                  | error "Variable name in Write not recoginzed" = undefined
                  | otherwise = undefined
         in (ex_var_name_JS var_name,r)

ex_TmemR :: [JSNode] -> ([JSNode], String)
ex_TmemR _ | trace 30 "ex_TmemR" False = undefined
ex_TmemR js = ex_obj_lu_JS js

ex_TmemW1 :: [JSNode] -> (String, String, [JSNode])
ex_TmemW1 _ | trace 30 "ex_TmemW1" False = undefined
ex_TmemW1 js = let
          (l,_o,r) = split_assignment js
          (var,m) = ex_field_of_var_JS l
          in (var,m,r)

ex_TmemW2 :: [JSNode] -> ([JSNode], String, [JSNode])
ex_TmemW2 _ | trace 30 "ex_TmemW2" False = undefined
ex_TmemW2 js = let
          (l,_o,r) = split_assignment js
          (var,m) = ex_obj_lu_JS l
          in (var,m,r)

ex_TmemX :: [JSNode] -> ([JSNode], String, [[JSNode]])
ex_TmemX j | trace 30 ("ex_TmemX" ++ show j) False = undefined
ex_TmemX j = ex_object_call_JS j
--ex_TmemX [obj,args] = (ex_obj_JS obj,ex_field_JS obj,ex_args_JS args)
--ex_TmemX js |trace 1 ("MemX not recognised" ++ show js)  True = undefined
--            | otherwise = undefined

ex_TfunX :: [JSNode] -> ([JSNode],[[JSNode]])
ex_TfunX _ | trace 30 "ex_TfunX" False = undefined
ex_TfunX js = ex_function_call_JS js

ex_TnewX :: [JSNode] -> ([JSNode],[[JSNode]])
ex_TnewX js | trace 30 ("ex_TnewX" ++ show js) False = undefined
ex_TnewX js = ex_new_call_JS js

-- Statements

ex_Tcond :: JSNode -> (JSNode,JSNode,JSNode)
ex_Tcond _ | trace 30 "ex_Tcond" False = undefined
ex_Tcond j = ex_if_comps_JS j

ex_TvarD :: JSNode -> (String,[JSNode])
ex_TvarD j | trace 30 ("ex_TvarD: " ++ show j) False = undefined
ex_TvarD j = ex_decl_comps_JS j

ex_TfunStmt :: JSNode -> (String,[String],JSNode)
ex_TfunStmt _ | trace 30 "ex_TfunD: " False = undefined
ex_TfunStmt j = ex_fun_comps_JS j

ex_TfunExpr :: [JSNode] -> (String,[String],JSNode)
ex_TfunExpr _ | trace 30 "ex_TfunD: " False = undefined
ex_TfunExpr [j] = ex_fun_comps_JS j
ex_TfunExpr _ | error "Function Expression not recognized" = undefined
              | otherwise = undefined


ex_TobjLit :: [JSNode] -> [(String,[JSNode])]
ex_TobjLit _ | trace 30 "ex_TobjD" False = undefined
ex_TobjLit [j] = ex_objDecl_JS j
ex_TobjLit _ | error "Object Literal not recognized" = undefined
             | otherwise = undefined

ex_Twhile :: JSNode -> (JSNode, JSNode)
ex_Twhile _ | trace 30 "ex_TWhile" False = undefined
ex_Twhile j = (extract_JSNode ex_while) j

ex_Tfor :: JSNode -> ([JSNode], JSNode,JSNode,JSNode)
ex_Tfor _ | trace 30 "ex_Tfor" False = undefined
ex_Tfor j = (extract_JSNode ex_for) j

ex_Treturn :: JSNode -> [[JSNode]]
ex_Treturn _ | trace 30 "ex_Return" False = undefined
ex_Treturn j = (extract_JSNode ex_return) j

----------------------------------------
-- component extractors
----------------------------------------

ex_TerOp :: [JSNode] -> ([[JSNode]],[[JSNode]],[[JSNode]])
ex_TerOp _ | trace 30 "ex_TerOp" False = undefined
ex_TerOp [j] = (extract_JSNode ex_terop) j
ex_TerOp _ | error "Ternary Operator not recognized" = undefined
           | otherwise = undefined

ex_terop :: Node -> ([[JSNode]],[[JSNode]],[[JSNode]])
ex_terop (JSExpressionTernary cond _qm true _colon false) = (split_expsequence cond,split_expsequence true,split_expsequence false)

ex_BinOp :: [JSNode] -> ([JSNode],[JSNode])
ex_BinOp _ | trace 30 "ex_BinOp" False = undefined
ex_BinOp [j] = (extract_JSNode ex_binop) j
ex_BinOp _ | error "Binary Operator not recognized" = undefined
           | otherwise = undefined

ex_binop :: Node -> ([JSNode],[JSNode])
ex_binop (JSExpressionBinary _s e1 _op e2) = (e1,e2)
ex_binop _ |trace 30 "binop not recognised" True = undefined
           | otherwise = undefined

ex_UnOp :: [JSNode] -> [JSNode]
ex_UnOp (j:js) = js

ex_intpostfixop :: Node -> [JSNode]
ex_intpostfixop (JSExpressionPostfix _s js _op) = js
ex_intpostfixop _ | error "Postfix Operator not recognized" = undefined
                  | otherwise = undefined

ex_PostfixOp :: [JSNode] -> [JSNode]
ex_PostfixOp _ | trace 30 "ex_IntPostfixOp" False = undefined
ex_PostfixOp [j] = (extract_JSNode ex_intpostfixop) j
ex_PostfixOp _ | error "Postfix operator not recognized" = undefined
                  | otherwise = undefined

ex_var_name :: Node -> String
ex_var_name n | trace 30 ("ex_var_name " ++ (show n)) False = undefined
ex_var_name (JSIdentifier s) = s
ex_var_name (JSLiteral "this") = "this"
ex_var_name _ | error "var_name not recognised" = undefined
              | otherwise = undefined

ex_var_name_JS :: JSNode -> String
ex_var_name_JS = extract_JSNode ex_var_name

ex_var_name_list :: [JSNode] -> [String]
ex_var_name_list [] = []
ex_var_name_list (x:xs) | is_irrellevant_JS x = ex_var_name_list xs
                        | otherwise = (ex_var_name_JS x):(ex_var_name_list xs)

----------------------------------------
-- Object access
----------------------------------------

-- simple field access to variable
ex_field_of_var :: Node -> (String,String)
ex_field_of_var (JSMemberDot [o] _dot field) = (ex_var_name_JS o, ex_var_name_JS field)
ex_field_of_var (JSMemberSquare [o] _bl field _br) = let 
  [[j]] = ex_Expression_JS field
  in (ex_var_name_JS o,ex_var_name_JS j)
ex_field_of_var _ | error "field_of_var not recognised" = undefined
                  | otherwise = undefined

ex_field_of_var_JS :: [JSNode] -> (String,String)
ex_field_of_var_JS [j] = (extract_JSNode ex_field_of_var) j
ex_field_of_var_JS _ | error "Field of Variable not recognized" = undefined
                     | otherwise = undefined

-- access to a members of the proceding object
ex_mem_acc :: Node -> String
ex_mem_acc (JSCallExpression "." _ [mem] []) = ex_var_name_JS mem
ex_mem_acc (JSCallExpression "[]" _ [mem] _) = ex_var_name_JS mem
ex_mem_acc _ | error "MemAcc not recognized" = undefined
             | otherwise = undefined

ex_mem_acc_JS :: JSNode -> String
ex_mem_acc_JS = extract_JSNode ex_mem_acc

-- direct object access in on JSNode
ex_obj_acc_JS :: JSNode -> ([JSNode],String)
ex_obj_acc_JS = extract_JSNode ex_obj_acc

ex_obj_acc :: Node -> ([JSNode],String)
ex_obj_acc (JSMemberDot ps _dot field) = (ps,ex_var_name_JS field)
ex_obj_acc (JSMemberSquare ps _lb field _rb) = let
  [[j]] = ex_Expression_JS field
  in (ps,ex_var_name_JS j)
ex_obj_acc _ | error "ObjAcc not recognised" = undefined
             | otherwise = undefined

-- indirect object lookup in [JSNode]
ex_obj_lu_JS :: [JSNode] -> ([JSNode],String)
ex_obj_lu_JS [] | error "Empty Object access" = undefined
ex_obj_lu_JS [j] = ex_obj_acc_JS j
ex_obj_lu_JS js = ex_obj_lu_last js

ex_obj_lu_last :: [JSNode] -> ([JSNode],String)
ex_obj_lu_last [] | error "ObjLU not recognized" = undefined
                  | otherwise = undefined
ex_obj_lu_last [j] = ([],ex_mem_acc_JS j)
ex_obj_lu_last (j:js) = let
               (obj,field) = ex_obj_lu_last js
               in (j:obj,field)
----------------------------------------
-- Funcions
----------------------------------------

-- return the expression of the function and a list of expressions of the arguments
ex_new_call_JS :: [JSNode] -> ([JSNode],[[JSNode]])
ex_new_call_JS ((NT (JSLiteral "new") _t _c):js) 
  | is_TfunX_JS js = ex_function_call_JS js
  | is_TmemX_JS js = ex_function_call_JS js --also include the field access into the function expression
  | otherwise = (js,[])  -- no parenthesis -> optional parameters omitted
ex_new_call_JS _ | error "New call not recognized" = undefined
                 | otherwise = undefined

ex_object_call_JS :: [JSNode] -> ([JSNode],String,[[JSNode]])
ex_object_call_JS (j:js) = let
                  (h,t) = head_tail (j:js)
                  (obj,m) = ex_obj_lu_JS h
                  in (obj,m,ex_argument_JS t)
ex_object_call_JS _ | error "object call not recognized" = undefined
                    | otherwise = undefined

ex_function_call_JS :: [JSNode] -> ([JSNode],[[JSNode]])
ex_function_call_JS js |trace 30 ("Function call " ++ show js) False = undefined
ex_function_call_JS (j:js) = let
                    (h,t) = head_tail (j:js)
                    in (h,ex_argument_JS t)
ex_function_call_JS _ | error "FunctionCall not recognized" = undefined
                      | otherwise = undefined                                                              

ex_argument :: Node -> [[JSNode]]
ex_argument n | trace 30 ("Argument: " ++ show n) False = undefined
ex_argument (JSArguments _lb args _rb) = 
        split_arguments args
ex_argument (JSCallExpression "()" [] [NN (JSArguments _lb args _rb)] []) = 
        split_arguments args
ex_argument j | error ("args not recognised" ++ show j) = undefined
              | otherwise = undefined

ex_argument_JS :: JSNode -> [[JSNode]]
ex_argument_JS = extract_JSNode ex_argument

----------------------------------------
-- Statements
----------------------------------------

-- expects to find a single statement in each of the branches
--   - True branch is either [stmt] or [stmt ;]
--   - Else branch is either [] or [else stmt] or [else stmt ;]
-- Boolean expression is wrapped in a JSExpression -> diguised as a Stmt
ex_if_comps :: Node -> (JSNode,JSNode,JSNode)
ex_if_comps (JSIf _if _lb bool _rb true_list []) = let
            true = ex_single_stmt true_list
            in (bool,true,NN (JSLiteral ""))
ex_if_comps (JSIf _if _lb bool _rb true_list (_elsee:false_list)) = let
            true = ex_single_stmt true_list
            false = ex_single_stmt false_list
            in (bool,true,false)
ex_if_comps js | error ("if components not recognized " ++ show js) = undefined
               | otherwise = undefined

ex_single_stmt :: [JSNode] -> JSNode
ex_single_stmt [j] = j
ex_single_stmt [j,j2] | is_semicolon_JS j2 = j
ex_single_stmt js | error ("Single Statement not recognized" ++ show js) = undefined
                  | otherwise = undefined

ex_if_comps_JS :: JSNode -> (JSNode, JSNode, JSNode)
ex_if_comps_JS = extract_JSNode ex_if_comps

ex_decl_comps :: Node -> (String,[JSNode])
ex_decl_comps j | trace 30 ("ex_decl_comps: " ++ show j) False = undefined
ex_decl_comps (JSVarDecl x d) = let ds = ex_varDecl d
                                in case ds of
                                  [] -> (ex_var_name_JS x,[])
                                  _ -> (ex_var_name_JS x,x:ds)
ex_decl_comps _ | error "decl_comps not recognised" = undefined
                | otherwise = undefined

ex_decl_comps_JS :: JSNode -> (String,[JSNode])
ex_decl_comps_JS = extract_JSNode ex_decl_comps

ex_fun_comps :: Node -> (String,[String],JSNode)
ex_fun_comps (JSFunction _function f _lb args _rb e) = (ex_var_name_JS f,ex_var_name_list args,e)
ex_fun_comps (JSFunctionExpression _function fns _lb args _rb e) = (ex_String_list fns,ex_var_name_list args,e)
ex_fun_comps _ | error "fun_comps not recognised" = undefined
               | otherwise = undefined

ex_fun_comps_JS :: JSNode -> (String,[String],JSNode)
ex_fun_comps_JS = extract_JSNode ex_fun_comps

ex_varDecl :: [JSNode] -> [JSNode]
ex_varDecl js | trace 30 ("ex_varDecl: " ++ show js) False = undefined
ex_varDecl (o:es) | trace 30 ("ex_varDecl: " ++ show o) True = ((NN (JSOperator o))):es
ex_varDecl [] | trace 30 "ex_varDecl: emty" True = []
ex_varDecl _ | error "varDecl not recognised" = undefined
             | otherwise = undefined

ex_objDecl :: Node -> [(String,[JSNode])]
ex_objDecl (JSObjectLiteral _lb fields _rb) = ex_fieldList fields
ex_objDecl _ | error "objDecl not recognised" = undefined
             | otherwise = undefined

ex_objDecl_JS :: JSNode -> [(String,[JSNode])]
ex_objDecl_JS = extract_JSNode ex_objDecl

ex_fieldList :: [JSNode] -> [(String,[JSNode])]
ex_fieldList [] =[]
ex_fieldList (x:xs) = case x of
  (NT (JSLiteral ",") _p _c) -> ex_fieldList xs
  _ -> (ex_fieldDecl_JS x):(ex_fieldList xs)

ex_fieldDecl :: Node -> (String,[JSNode])
ex_fieldDecl j | trace 30 ("\nex_fieldDecl : " ++ (show j)) False = undefined
ex_fieldDecl (JSPropertyNameandValue a _dev e) = (ex_String_JS a,e)
ex_fieldDecl _ | error "fieldDecl not recognised" = undefined
               | otherwise = undefined

ex_fieldDecl_JS :: JSNode -> (String,[JSNode])
ex_fieldDecl_JS = extract_JSNode ex_fieldDecl

ex_string :: Node -> String
ex_string (JSStringLiteral _lim s) =s
ex_string (JSIdentifier s) = s
ex_string _ | error "String not recognised" = undefined
            | otherwise = undefined

ex_String_list :: [JSNode] -> String
ex_String_list = Prelude.foldr (\j prv -> (ex_String_JS j) ++ prv) ""

ex_String_JS :: JSNode -> String
ex_String_JS = extract_JSNode ex_string

ex_TstringLit :: [JSNode] -> String
ex_TstringLit [j] = (extract_JSNode ex_stringD) j
ex_TstringLit _ | error "String Literal not recoginzed" = undefined
                | otherwise = undefined

ex_stringD :: Node -> String
ex_stringD (JSStringLiteral _lim s) = s
ex_stringD _ | error "stringD not recognised" = undefined
             | otherwise = undefined

ex_while :: Node -> (JSNode,JSNode)
ex_while (JSWhile _while _rb bool _lb e) = (bool,e)
ex_while _ | error "while not recognised" = undefined
           | otherwise = undefined

-- Return a sequence of Statements (multipl var decls)
ex_for :: Node -> ([JSNode],JSNode,JSNode,JSNode)
ex_for (JSFor _for _rb [e1] _sem1 [e2] _sem2 [e3] _lb body) = ([e1],e2,e3,body) 
ex_for (JSForVar _for _var _rb e1 _sem1 [e2] _sem2 [e3] _lb body) = (split_variables e1,e2,e3,body)
ex_for _ | error "for not recognized" = undefined
         | otherwise = undefined

ex_return :: Node -> [[JSNode]]
ex_return (JSReturn _lit exprs _lim) = split_expsequence exprs
ex_return _ | error "return not recognised" = undefined
            | otherwise = undefined

ex_fid :: Node -> String
ex_fid (JSFunction _function f _lb _args _rb _e) =
  ex_var_name_JS f
ex_fid (JSFunctionExpression _function [] _lb _args _rb _e) =
  showCode (JSFunctionExpression _function [] _lb _args _rb _e)
ex_fid (JSFunctionExpression _function fns _lb _args _rb _e) =
  ex_String_list fns
ex_fid j = showCode j

ex_fID :: [JSNode] -> String
ex_fID [] = ""
ex_fID (j:js) = ((extract_JSNode ex_fid) j) ++ (ex_fID js)

ex_Statements :: JSNode -> [JSNode]
ex_Statements (NT n _ _) = ex_Statements (NN n)
ex_Statements (NN n) = ex_statements n

ex_statements :: Node -> [JSNode]
ex_statements (JSArguments _lb _xs _rb) = []
ex_statements (JSArrayLiteral _lb _xs _rb) = []
ex_statements (JSBlock _lb xs _rb) = split_sequence xs
ex_statements (JSBreak _b _x1s _as) = []
ex_statements (JSCallExpression _s _os _xs _cs) = []
ex_statements (JSCase _ca x1 _c x2s) = x1:(split_sequence x2s)
ex_statements (JSCatch _c _lb _x1 _x2s _rb x3) = [x3]
ex_statements (JSContinue _c _xs _as) = []
ex_statements (JSDecimal _s) = []
ex_statements (JSDefault _d _c xs) = split_sequence xs
ex_statements (JSDoWhile _d x1 _w _lb x2 _rb _x3) = [x1,x2]
ex_statements (JSElision _c) = []
ex_statements (JSExpression _xs) = []
ex_statements (JSExpressionBinary _s _x2s _op _x3s) = []
ex_statements (JSExpressionParen _lp x _rp) = [x]
ex_statements (JSExpressionPostfix _s _xs _op) = []
ex_statements (JSExpressionTernary _x1s _q _x2s _c _x3s) = []
ex_statements (JSFinally _f x) = [x]
ex_statements (JSFor _f _lb _x1 _s1 _x2 _s2 _x3 _rb x4) = [x4]
ex_statements (JSForIn _f _lb _x1s _i x2 _rb x3) = [x2,x3]
ex_statements (JSForVar _f _lb _v x1 _s1 _x2 _s2 _x3 _rb x4) = [x4] ++ split_variables x1
ex_statements (JSForVarIn _f _lb _v x1 _i x2 _rb x3) = [x1,x2,x3]
ex_statements (JSFunction _f _x1 _lb _x2s _rb x3) = [x3]
ex_statements (JSFunctionExpression _f _x1s _lb _x2s _rb x3) = [x3]
ex_statements (JSHexInteger _s) = []
ex_statements (JSOctal _s) = []
ex_statements (JSIdentifier _s) = []
ex_statements (JSIf _i _lb x1 _rb x2s x3s) = x1:((split_sequence x2s) ++ (split_sequence x3s))
ex_statements (JSLabelled _x1 _c x2) = [x2]
ex_statements (JSLiteral _s) = []
ex_statements (JSMemberDot _x1s _d _x2 ) = []
ex_statements (JSMemberSquare _x1s _lb x2 _rb) = [x2]
ex_statements (JSObjectLiteral _lb _xs _rb) = []
ex_statements (JSOperator _n) = []
ex_statements (JSPropertyNameandValue _x1 _colon _x2s) = []
ex_statements (JSPropertyAccessor _s _x1 _lb1 _x2s _rb1 x3) = [x3]
ex_statements (JSRegEx _s) = []
ex_statements (JSReturn _r _xs _as) = []
ex_statements (JSSourceElementsTop xs) = split_sequence xs
ex_statements (JSStringLiteral _c _s) = []
ex_statements (JSSwitch _s _lb x _rb x2) = [x,x2]
ex_statements (JSThrow _t _x) = []
ex_statements (JSTry _t x1 x2s) = x1:x2s
ex_statements (JSUnary _s _x) = []
ex_statements (JSVarDecl _x1 _x2s) = []
ex_statements (JSVariables _n xs _as) = split_variables xs
ex_statements (JSWhile _w _lb x1 _rb x2) = [x1,x2]
ex_statements (JSWith _w _lb x1 _rb x2s) = x1:(filter_irrelevant x2s)
--ex_statements j | error ("Not recognized[Stmt] " ++ show j) = undefined

ex_Expressions :: JSNode -> [[JSNode]]
ex_Expressions (NT n _ _) = ex_Expressions (NN n)
ex_Expressions (NN n) = ex_expressions n


ex_expressions :: Node -> [[JSNode]]
ex_expressions (JSArguments _lb xs _rb) = split_arguments xs
ex_expressions (JSArrayLiteral _lb xs _rb) = split_array xs
ex_expressions (JSBlock _lb _xs _rb) = []
ex_expressions (JSBreak _b _x1s _as) = []
ex_expressions (JSCallExpression _s _os xs _cs) = [xs]
ex_expressions (JSCase _ca _x1 _c _x2s) = []
ex_expressions (JSCatch _c _lb x1 x2s _rb _x3) = [[x1],x2s]
ex_expressions (JSContinue _c xs _as) = [xs]
ex_expressions (JSDecimal _s) = []
ex_expressions (JSDefault _d _c _xs) = []
ex_expressions (JSDoWhile _d _x1 _w _lb _x2 _rb _x3) = []
ex_expressions (JSElision _c) = []
ex_expressions (JSExpression xs) = split_expsequence xs
ex_expressions (JSExpressionBinary _s x2s _op x3s) = [x2s,x3s]
ex_expressions (JSExpressionParen _lp _x _rp) = []
ex_expressions (JSExpressionPostfix _s xs _op) = [xs]
ex_expressions (JSExpressionTernary x1s _q x2s _c x3s) = [x1s,x2s,x3s]
ex_expressions (JSFinally _f _x) = []
ex_expressions (JSFor _f _lb x1s _s1 x2s _s2 x3s _rb _x4) = [x1s,x2s,x3s]
ex_expressions (JSForIn _f _lb _x1s _i_ _x2 _rb _x3) = []
ex_expressions (JSForVar _f _lb _v _x1s _s1 x2s _s2 x3s _rb _x4) = [x2s,x3s]
ex_expressions (JSForVarIn _f _lb _v _x1 _i _x2 _rb _x3) = []
ex_expressions (JSFunction _f _x1 _lb x2s _rb _x3) = split_arguments x2s
ex_expressions (JSFunctionExpression _f _x1s _lb x2s _rb _x3) = split_arguments x2s
ex_expressions (JSHexInteger _s) = []
ex_expressions (JSOctal _s) = []
ex_expressions (JSIdentifier _s) = []
ex_expressions (JSIf _i _lb _x1 _rb _x2s _x3s) = []
ex_expressions (JSLabelled _x1 _c _x2) = []
ex_expressions (JSLiteral _s) = []
ex_expressions (JSMemberDot x1s _d _x2 ) = [x1s]
ex_expressions (JSMemberSquare x1s _lb _x2 _rb) = [x1s]
ex_expressions (JSObjectLiteral _lb xs _rb) = split_expsequence xs
ex_expressions (JSOperator _n) = []
ex_expressions (JSPropertyNameandValue _x1 _colon x2s) = [x2s]
ex_expressions (JSPropertyAccessor _s _x1 _lb1 x2s _rb1 _x3) = split_arguments x2s
ex_expressions (JSRegEx _s) = []
ex_expressions (JSReturn _r xs _as) = split_expsequence xs
ex_expressions (JSSourceElementsTop _xs) = []
ex_expressions (JSStringLiteral _c _s) = []
ex_expressions (JSSwitch _s _lb _x _rb _x2) = []
ex_expressions (JSThrow _t _x) = []
ex_expressions (JSTry _t _x1 _x2s) = []
ex_expressions (JSUnary _s _x) = []
ex_expressions (JSVarDecl _x1 x2s) = let (_l,_o,r) = split_assignment x2s in [r]
ex_expressions (JSVariables _n _xs _as) = []
ex_expressions (JSWhile _w _lb _x1 _rb _x2) = []
ex_expressions (JSWith _w _lb x1 _rb x2s) = [[x1],x2s]

ex_JSId :: JSNode -> String
ex_JSId = extract_JSNode ex_jsid

ex_jsid :: Node -> String
ex_jsid (JSArguments _lb _xs _rb) = "JSArguments"
ex_jsid (JSArrayLiteral _lb _xs _rb) = "JSArrayLiteral"
ex_jsid (JSBlock _lb _xs _rb) = "JSBlock"
ex_jsid (JSBreak _b _x1s _as) = "JSBreak"
ex_jsid (JSCallExpression _s _os _xs _cs) = "JSCallExpression"
ex_jsid (JSCase _ca _x1 _c _x2s) = "JSCase"
ex_jsid (JSCatch _c _lb _x1 _x2s _rb _x3) = "JSCatch"
ex_jsid (JSContinue _c _xs _as) = "JSContinue"
ex_jsid (JSDecimal _s) = "JSDecimal"
ex_jsid (JSDefault _d _c _xs) = "JSDefault"
ex_jsid (JSDoWhile _d _x1 _w _lb _x2 _rb _x3) = "JSDoWhile"
ex_jsid (JSElision _c) = "JSElision"
ex_jsid (JSExpression _xs) = "JSExpression"
ex_jsid (JSExpressionBinary _s _x2s _op _x3s) = "JSExpressionBinary"
ex_jsid (JSExpressionParen _lp _x _rp) = "JSExpressionParen"
ex_jsid (JSExpressionPostfix _s _xs _op) = "JSExpressionPostfox"
ex_jsid (JSExpressionTernary _x1s _q _x2s _c _x3s) = "JSExpressionTernary"
ex_jsid (JSFinally _f _x) = "JSFinally"
ex_jsid (JSFor _f _lb _x1s _s1 _x2s _s2 _x3s _rb _x4) = "JSFor"
ex_jsid (JSForIn _f _lb _x1s _i _x2 _rb _x3) = "JSForIn"
ex_jsid (JSForVar _f _lb _v _x1s _s1 _x2s _s2 _x3s _rb _x4) = "JSForVar"
ex_jsid (JSForVarIn _f _lb _v _x1 _i _x2 _rb _x3) = "JSForVarIn"
ex_jsid (JSFunction _f _x1 _lb _x2s _rb _x3) = "JSFunction"
ex_jsid (JSFunctionExpression _f _x1s _lb _x2s _rb _x3) = "JSFunctionExpression"
ex_jsid (JSHexInteger _s) = "JSHexInteger"
ex_jsid (JSOctal _s) = "JSOctal"
ex_jsid (JSIdentifier _s) = "JSIndentifier"
ex_jsid (JSIf _i _lb _x1 _rb _x2s _x3s) = "JSIf"
ex_jsid (JSLabelled _x1 _c _x2) = "JSLabeled"
ex_jsid (JSLiteral s) = "JSLiteral " ++ s
ex_jsid (JSMemberDot _x1s _d _x2 ) = "JSMemberDot"
ex_jsid (JSMemberSquare _x1s _lb _x2 _rb) = "JSMemberSquare"
ex_jsid (JSObjectLiteral _lb _xs _rb) = "JSObjectLiteral"
ex_jsid (JSOperator _n) = "JSOberator"
ex_jsid (JSPropertyNameandValue _x1 _colon _x2s) = "JSPropertyNameandValue"
ex_jsid (JSPropertyAccessor _s _x1 _lb1 _x2s _rb1 _x3) = "JSPropertyAccessor"
ex_jsid (JSRegEx _s) = "JSRegEx"
ex_jsid (JSReturn _r _xs _as) = "JSReturn"
ex_jsid (JSSourceElementsTop _xs) = "JSSourceElementsTop"
ex_jsid (JSStringLiteral _c _s) = "JSStringLiteral"
ex_jsid (JSSwitch _s _lb _x _rb _x2) = "JSSwitch"
ex_jsid (JSThrow _t _x) = "JSThrow"
ex_jsid (JSTry _t _x1 _x2s) = "JSTry"
ex_jsid (JSUnary _s _x) = "JSUnary"
ex_jsid (JSVarDecl _x1 _x2s) = "JSVarDecl"
ex_jsid (JSVariables _n _xs _as) = "JSVariables"
ex_jsid (JSWhile _w _lb _x1 _rb _x2) = "JSWhile"
ex_jsid (JSWith _w _lb _x1 _rb _x2s) = "JSWith"

----------------------------------------
-- Meta functions
----------------------------------------

extract_JSNode :: (Node -> t) -> JSNode -> t
extract_JSNode f (NN n) = f n
extract_JSNode f (NT n _p _c) = extract_JSNode f (NN n)

-- extract the path to a field of a 
-- ex_path_List :: [JSNode] -> String
-- ex_path_List [x] = ex_path_JS x
-- ex_path_List (_:xs) = ex_path_List xs
-- ex_path_List [] = ""

-- ex_path_JS :: JSNode -> String
-- ex_path_JS (NN n) = ex_path n
-- ex_path_JS (NT n _ _) = ex_path n

-- ex_path :: Node -> String
-- ex_path (JSIdentifier s) = s
-- ex_path (JSMemberDot objs _sep field) = ex_path_List objs ++ "." ++ ex_path_JS field
-- ex_path (JSMemberSquare objs _lb field _rb) = ex_path (JSMemberDot objs _lb field)

ex_code :: JSNode -> String
ex_code = ss

ex_code_list :: [JSNode] -> String
ex_code_list [] = ""
ex_code_list (x:xs) = ex_code x ++ ex_code_list xs

ss :: JSNode -> String
ss (NN node    ) = showCode node
ss (NT node _ _) = showCode node

sss :: [JSNode] -> String
sss xs = (concatMap ss xs)

showCode :: Node -> String
showCode (JSArguments lb xs rb) = ss lb ++ sss xs ++ ss rb
showCode (JSArrayLiteral lb xs rb) = ss lb ++ sss xs ++ ss rb
showCode (JSBlock lb xs rb) = sss lb ++ sss xs ++ sss rb
showCode (JSBreak b x1s as) =  ss b ++ sss x1s ++ ss as
showCode (JSCallExpression _s os xs cs) = sss os ++ sss xs ++ sss cs
showCode (JSCase ca x1 c x2s) = ss ca ++ ss x1 ++ ss c ++ sss x2s
showCode (JSCatch c lb x1 x2s rb x3) = ss c ++ ss lb ++ ss x1 ++ sss x2s ++ ss rb ++ ss x3
showCode (JSContinue c xs as) = ss c ++ sss xs ++ ss as
showCode (JSDecimal s) = s
showCode (JSDefault d c xs) = ss d ++ ss c ++ sss xs
showCode (JSDoWhile d x1 w lb x2 rb x3) = ss d ++ ss x1 ++ ss w ++ ss lb ++ ss x2 ++ ss rb ++ ss x3
showCode (JSElision c) = ss c
showCode (JSExpression xs) = sss xs
showCode (JSExpressionBinary s x2s op x3s) = s ++ sss x2s ++ ss op ++ sss x3s
showCode (JSExpressionParen lp x rp) = ss lp ++ ss x ++ ss rp
showCode (JSExpressionPostfix s xs op) = s ++ sss xs ++ ss op
showCode (JSExpressionTernary x1s q x2s c x3s) = sss x1s ++ ss q ++ sss x2s ++ ss c ++ sss x3s
showCode (JSFinally f x) = ss f ++ ss x
showCode (JSFor f lb x1s s1 x2s s2 x3s rb x4) = ss f ++ ss lb ++ sss x1s ++ ss s1 ++ sss x2s ++ ss s2 ++ sss x3s ++ ss rb ++ ss x4 ++ ss lb
showCode (JSForIn f lb x1s i x2 rb x3) = ss f ++ ss lb ++ sss x1s ++ ss i ++ ss x2 ++ ss rb ++ ss x3
showCode (JSForVar f lb v x1s s1 x2s s2 x3s rb x4) = ss f ++ ss lb ++ ss v ++ sss x1s ++ ss s1 ++ sss x2s ++ ss s2 ++ sss x3s ++ ss rb ++ ss x4
showCode (JSForVarIn f lb v x1 i x2 rb x3) = ss f ++ ss lb ++ ss v ++ ss x1 ++ ss i ++ ss x2 ++ ss rb ++ ss x3
showCode (JSFunction f x1 lb x2s rb x3) = ss f ++ ss x1 ++ ss lb ++ sss x2s ++ ss rb ++ ss x3
showCode (JSFunctionExpression f x1s lb x2s rb x3) = ss f ++ sss x1s ++ ss lb ++ sss x2s ++ ss rb ++ ss x3
showCode (JSHexInteger s) = s
showCode (JSOctal s) = s
showCode (JSIdentifier s) = " " ++ s ++ " "
showCode (JSIf i lb x1 rb x2s x3s) = ss i ++ ss lb ++ ss x1 ++ ss rb ++ sss x2s ++ sss x3s
showCode (JSLabelled x1 c x2) = ss x1 ++ ss c ++ ss x2
showCode (JSLiteral s) = " " ++ s ++ " "
showCode (JSMemberDot x1s d x2 ) = sss x1s ++ ss d  ++ ss x2
showCode (JSMemberSquare x1s lb x2 rb) = sss x1s ++ ss lb ++ ss x2 ++ ss rb
showCode (JSObjectLiteral lb xs rb) = ss lb ++ sss xs ++ ss rb
showCode (JSOperator n) = ss n
showCode (JSPropertyNameandValue x1 colon x2s) = ss x1 ++ ss colon ++ sss x2s
showCode (JSPropertyAccessor s x1 lb1 x2s rb1 x3) = ss s ++ ss x1 ++ ss lb1 ++ sss x2s ++ ss rb1 ++ ss x3
showCode (JSRegEx s) = s
showCode (JSReturn r xs as) = ss r ++ sss xs ++ ss as
showCode (JSSourceElementsTop xs) = sss xs
showCode (JSStringLiteral _c s) = s
showCode (JSSwitch s lb x rb x2) = ss s ++ ss lb ++ ss x ++ ss rb ++ ss x2
showCode (JSThrow t x) = ss t ++ ss x
showCode (JSTry t x1 x2s) = ss t ++ ss x1 ++ sss x2s
showCode (JSUnary s x) = s ++ ss x
showCode (JSVarDecl x1 x2s) = ss x1 ++ sss x2s
showCode (JSVariables n xs as) = ss n ++ sss xs ++ ss as
showCode (JSWhile w lb x1 rb x2) = ss w ++ ss lb ++ ss x1 ++ ss rb ++ ss x2
showCode (JSWith w lb x1 rb x2s) = ss w ++ ss lb ++ ss x1 ++ ss rb ++ sss x2s

ex_SourceElementsTop :: Node -> [JSNode]
ex_SourceElementsTop (JSSourceElementsTop js) = split_sequence js
ex_SourceElementsTop _ | error "SourceElementsTop not recognized" = undefined
                       | otherwise = undefined

ex_Expression :: Node -> [[JSNode]]
ex_Expression (JSExpression js) = split_expsequence js
ex_Expression _ | error "Expression not recognized" = undefined
                | otherwise = undefined

ex_Expression_JS :: JSNode -> [[JSNode]]
ex_Expression_JS = extract_JSNode ex_Expression

ex_Expression_single :: [JSNode] -> [[JSNode]]
ex_Expression_single [j] = ex_expression_single j

ex_expression_single :: JSNode -> [[JSNode]]
ex_expression_single = extract_JSNode ex_Expression 

ex_ExpressionParen_single :: [JSNode] -> [[JSNode]]
ex_ExpressionParen_single [j] = ex_expressionParen_single j

ex_expressionParen_single :: JSNode -> [[JSNode]]
ex_expressionParen_single = extract_JSNode ex_ExpressionParen 

ex_Variables :: Node -> [JSNode]
ex_Variables (JSVariables _var js _cont) = split_variables js
ex_Variables _ | error "Variables not recognized" = undefined
               | otherwise = undefined

ex_Block :: Node -> [JSNode]
ex_Block (JSBlock _lb js _rb) = split_sequence js
ex_Block _ | error "Block not recognized" = undefined
           | otherwise = undefined

ex_ExpressionParen :: Node -> [[JSNode]]
ex_ExpressionParen (JSExpressionParen _lb (NN (JSExpression js)) _rb) = split_expsequence js
ex_ExpressionParen _ | error "ExpressionParen not recognized" = undefined
                     | otherwise = undefined
