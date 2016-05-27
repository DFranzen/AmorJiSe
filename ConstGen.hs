module ConstGen (
  constGen,
) where

import Language.JavaScript.Parser.AST
import Language.JavaScript.Parser.AST
import Language.JavaScript.Parser.SrcLocation

--import Language.JavaScript.Parser.SrcLocation
import JST0_types
import JST0_type_aux
import JST0_context
import JST0_constrain

import Debugging

import Conditionals
import Extraction

-- type
-- updated Environment
-- updated type variable count
-- constrains_types
type Con_out = (Int, Type, Context, [Constrain])
type Con_in = (Int, Context)


constGen :: Con_in -> JSNode -> Con_out
constGen (_a,_gamma) _j | trace 10 "constGen" False = undefined
constGen (a ,gamma ) j = let
  (a1,gamma1) = p1_Statement (a ,gamma ) j
  (a2,gamma2) = p2_Statement (a1,gamma1) j
  in cg_Statement (a2,gamma2) j

cg_Statement :: Con_in -> JSNode -> Con_out
cg_Statement (_a,_gamma) j | trace 10 ("Statement : " ++ (show j)) False = undefined
cg_Statement (a,gamma) (NT n _l _c) | trace 30 "JSNode NT" True = cg_Statement (a,gamma) (NN n)
cg_Statement (a,gamma) (NN n)
  -- boxes
  | is_SourceElementsTop_JS (NN n) = cg_Stmt_mult (a,gamma) (ex_SourceElementsTop n)
  | is_Variables_JS         (NN n) = cg_Stmt_mult (a,gamma) (ex_Variables         n)
  | is_Block_JS             (NN n) = cg_Stmt_mult (a,gamma) (ex_Block             n)
  | is_Expression_JS        (NN n) = cg_Exp_Stmt  (a,gamma) (ex_Expression        n)
  | is_ExpressionParen_JS   (NN n) = cg_Exp_Stmt  (a,gamma) (ex_ExpressionParen   n)

  -- unneccessary
  | is_emptyLiteral_JS (NN n) = cg_empty (a,gamma)
  | is_semicolon_JS    (NN n) = cg_empty (a,gamma)

  -- statements
  | is_TvarD_JS   (NN n) = cg_TvarD   (a,gamma) (ex_TvarD   (NN n))
  | is_Tcond_JS   (NN n) = cg_Tcond   (a,gamma) (ex_Tcond   (NN n))
  | is_Twhile_JS  (NN n) = cg_Twhile  (a,gamma) (ex_Twhile  (NN n))
  | is_Tfor_JS    (NN n) = cg_Tfor    (a,gamma) (ex_Tfor    (NN n))
  | is_Treturn_JS (NN n) = cg_Treturn (a,gamma) (ex_Treturn (NN n))

  | is_funStmt_JS (NN n) = cg_funStmt (a,gamma) (ex_TfunStmt (NN n))
cg_Statement (a,gamma) j | error ("CG: Not handled " ++ show j) = (a,JST0_None,gamma,[])
                         | otherwise = undefined

-- analyse a sequence of Stmts. Assume every element of this list constains a Stmt
cg_Stmt_mult :: Con_in -> [JSNode] -> Con_out
cg_Stmt_mult (_a,_gamma) _e1 | trace 10 ("Stmt_mult") False = undefined
cg_Stmt_mult (a,gamma) [] = (a,JST0_None,gamma,[])
cg_Stmt_mult (a,gamma) [j] = cg_Statement (a,gamma) j
cg_Stmt_mult (a,gamma) (j:js) = let 
  (a1,t1,gamma1,c_1) = cg_Statement (a ,gamma ) j
  (a2,t2,gamma2,c_2) = cg_Stmt_mult (a1,gamma1) js
  (a3,t3,       c_3) = seq_type a2 t1 t2
  in (a3,t3,gamma2,concat[c_1,c_2,c_3])

-- analyse an Exp sequence as Statement
cg_Exp_Stmt :: Con_in -> [[JSNode]] -> Con_out
cg_Exp_Stmt (_a,_gamma) _js  | trace 10 "Exp_Stmt" False = undefined
cg_Exp_Stmt (a,gamma) js = let
  (a1,t1,g1,c1) = cg_Exp_mult (a,gamma) js
  in (a1,JST0_None,g1,c1)

-- analyse an expression (Exp sequences have already been split up)
cg_Expression :: Con_in -> [JSNode] -> Con_out
cg_Expression (_a,_gamma) js | trace 10 ("Expression : " ++ show js) False = undefined
cg_Expression (a,gamma) js_dirty = let
  js = filter_irrelevant js_dirty
  res
    | is_Expression_single_JS       js = cg_Exp_mult  (a,gamma) (ex_Expression_single        js)
    | is_ExpressionParen_single_JS  js = cg_Exp_mult  (a,gamma) (ex_ExpressionParen_single   js)

    | is_Tnull_JS      js = cg_Tnull      (a,gamma)
    | is_Tint_JS       js = cg_Tint       (a,gamma)
    | is_TboolLit_JS   js = cg_TboolLit   (a,gamma)
    | is_TstringLit_JS js = cg_TstringLit (a,gamma) (ex_TstringLit js)
    | is_TobjLit_JS    js = cg_TobjLit    (a,gamma) (ex_TobjLit    js)

    | is_TvarR_JS  js = cg_TvarR  (a,gamma) (ex_TvarR  js)
    | is_TvarW_JS  js = cg_TvarW  (a,gamma) (ex_TvarW  js)
    | is_TmemR_JS  js = cg_TmemR  (a,gamma) (ex_TmemR  js)
    | is_TmemW1_JS js = cg_TmemW1 (a,gamma) (ex_TmemW1 js)
    | is_TmemW2_JS js = cg_TmemW2 (a,gamma) (ex_TmemW2 js)
    | is_TmemX_JS  js = cg_TmemX  (a,gamma) (ex_TmemX  js)
    | is_TfunX_JS  js = cg_TfunX  (a,gamma) (ex_TfunX  js)
    | is_TnewX_JS  js = cg_TfunX  (a,gamma) (ex_TnewX  js)

    | is_funExpr_JS js = cg_funExpr (a,gamma) (ex_TfunExpr js)

    | is_OPPlus_JS       js = cg_OPPlus       (a,gamma) (ex_BinOp js)
    | is_OPArithmetic_JS js = cg_OPArithmetic (a,gamma) (ex_BinOp js)
    | is_OPComparison_JS js = cg_OPComparison (a,gamma) (ex_BinOp js)
    | is_OPLogic_JS      js = cg_OPLogic      (a,gamma) (ex_BinOp js)
    | is_OPBang_JS       js = cg_OPBang       (a,gamma) (ex_UnOp  js)
    | is_OPSign_JS       js = cg_OPSign       (a,gamma) (ex_UnOp  js)
    | is_OPCond_JS       js = cg_OPCond       (a,gamma) (ex_TerOp js)
    | is_OPIntPostfix_JS js = cg_OPIntPF      (a,gamma) (ex_PostfixOp  js)

    | is_Statement_single js = cg_Stmt_mult (a,gamma) js
    | js == [] = (a,JST0_None,gamma,[])
    | error (show js) = undefined
  in res

-- analyse a sequence of Expressions. Assume each element of the list contains one Expression. Return the type of the sequence i.e. the last expression's type
cg_Exp_mult :: Con_in -> [[JSNode]] -> Con_out
cg_Exp_mult (_a,_gamma) _e1 | trace 10 ("Exp_mult") False = undefined
cg_Exp_mult (a,gamma) [] = (a,JST0_None,gamma,[])
cg_Exp_mult (a,gamma) [j] = cg_Expression (a,gamma) j
cg_Exp_mult (a,gamma) (j:js) = let 
  (a1,t1,gamma1,c_1) = cg_Expression (a ,gamma ) j
  (a2,t2,gamma2,c_2) = cg_Exp_mult   (a1,gamma1) js
  in (a2,t2,gamma2,concat[c_1,c_2])

-- Analyse a list of Expressions, return one type for each element of the list
cg_Exp_list :: Con_in -> [[JSNode]] ->(Int,[Type],Context,[Constrain])
cg_Exp_list (a,gamma) jss | trace 10 "Exp_list" False = undefined
cg_Exp_list (a,gamma) [] = (a,[],gamma,[])
cg_Exp_list (a,gamma) (js:jss) = let
  (a1,t1,g1,c1) = cg_Expression (a,gamma) js
  (a2,t2,g2,c2) = cg_Exp_list   (a1,g1) jss
  in (a2,t1:t2,g2,concat [c1,c2])

-- Analyse a list of variable definitions. The VarDecl head has already been extracted.
cg_TVariables :: Con_in -> [JSNode] -> Con_out
cg_TVariables (_a,_gamma) _e1 | trace 10 ("TVariables") False = undefined
cg_TVariables (a,gamma) e = let 
  ([e1],e2) = split_comma e
  (a1,t1,gamma1,c_1) = cg_Statement (a ,gamma ) e1
  (a0,t0,gamma0,c_0) | e2 == [] = (a1,t1,gamma1,[])
                     | otherwise = cg_TVariables (a1,gamma1) e2
  in (a0,t0,gamma0,concat[c_1,c_0])

----------------------------------------
-- Rules for constraint generation
----------------------------------------

cg_empty :: Con_in -> Con_out
cg_empty (_a,_gamma) | trace 10 "cg_empty" False = undefined
cg_empty (a,gamma) = (a,JST0_None,gamma,[])

cg_Tnull :: Con_in -> Con_out
cg_Tnull (_a,_gamma) | trace 10 ("Tnull\n") False = undefined
cg_Tnull (a,gamma) = let
  -- create new TVs
  o = (JST0_TV a "Null Object")
  a0 = a + 1
  
  c = [IsObject o]
  in (a0,o,gamma,c)

cg_Tint :: Con_in -> Con_out
cg_Tint (_a,_gamma) | trace 10 ("cg_Tint") False = undefined
cg_Tint (a,gamma) = (a,JST0_Int,gamma,[])

cg_TboolLit :: Con_in -> Con_out
cg_TboolLit (_a,_gamma) | trace 10 ("cg_BoolLit") False = undefined
cg_TboolLit (a,gamma) = (a,JST0_Bool,gamma,[])

cg_TvarR :: Con_in -> String -> Con_out
cg_TvarR (_a,_gamma) var | trace 10 ("cg_TvarR " ++ var) False = undefined
cg_TvarR (a,gamma) var = let
  -- create new variables
  t1 = (JST0_TV a (var ++ " copy to be stored back"))
  t2 = (JST0_TV (a+1) (var ++ " copy to be computed with"))
  a0 = a+2
  -- infer type
  (t_cand,psi_cand) = var_get gamma var
  t | psi_cand == Definite = t_cand
    | error ("Read from uninitialized variable: " ++ var) = undefined
    | otherwise = undefined
  gamma1 = var_set gamma var (t1,Definite)
  -- constraints
  c = [SubType t1 t,
       SubType t t1,
       SubType t2 t,
       SubType t t2]
  in (a0,t2,gamma1,c)

cg_TvarW :: Con_in -> (String,[JSNode]) -> Con_out
cg_TvarW (_a,_gamma) (x,_e) | trace 10 ("TvarW" ++ x) False = undefined
cg_TvarW (a,gamma) (x,e) = let
  -- create new variables
  txasse = (JST0_TV a (x ++ "=" ++ show e))
  txp    = (JST0_TV (a+1) (x ++ " updated"))
  a0 = a + 2;
  -- infer types
  (a1,te,gamma1,c_1) = cg_Expression (a0,gamma) e
  (tx,psi) = var_get gamma1 x
  gammap = var_set gamma1 x (tx,Definite)
  --constraints
  c = [SubType te tx, -- from the original rule
       SubType te txasse,  -- sharing translates into equality
       SubType txasse te,
       SubType txp te,
       SubType te txp]
  in (a1,txasse,gammap,concat[c_1,c])

cg_TmemR :: Con_in -> ([JSNode],String) -> Con_out
cg_TmemR (_a,_gamma) (_e,m) | trace 10 ("TmemR" ++ show m) False = undefined
cg_TmemR (a,gamma) (e,m) = let
  -- create new variables
  t2 = JST0_TV a ("MemberRead " ++ show m)
  a0 = a+1
  -- infer type
  (a1,o,gamma1,c_1) = cg_Expression (a0,gamma) e
  c = [SubType o (object_singleton NotRec m t2 Definite)]
  in (a1,t2,gamma1,concat [c_1,c])

cg_TmemW1 :: Con_in -> (String,String,[JSNode]) -> Con_out
cg_TmemW1 (_a,_gamma) (var,m,_e) | trace 10 ("TmemW1 " ++ var ++ "." ++ m) False = undefined
cg_TmemW1 (a,gamma) (var,m,e) = let
  -- create new variables
  tm = (JST0_TV a (var ++ "." ++ m))
  txp = (JST0_TV (a+1) var)
  txasse = (JST0_TV (a+2) (var ++ "." ++ m ++ "=e"))
  --tmp = (JST0_TV (a+2) (var ++ "." ++ m))
  a0 = a+3
  --infer type
  (a1,te,gamma1,c_1) = cg_Expression (a0,gamma) e
  tx = var_get_definite gamma1 var
  gamma2 = var_set gamma1 var (txp,Definite)
  -- constraints
  c = [SubType te tm,
       SubType tx  (object_singleton NotRec m tm Potential),
       SubType txp (object_singleton NotRec m tm Definite),
       SubType te txasse,
       MemberExtend txp m tx]
  in (a1,te,gamma2,concat [c_1,c])

cg_TmemW2 :: Con_in -> ([JSNode],String,[JSNode]) -> Con_out
cg_TmemW2 (_a,_gamma) (_e1,m,_e2) | trace 10 ("TmemW2 " ++ m) False = undefined
cg_TmemW2 (a,gamma) (e1,m,e2) = let
  -- create new variables
  tm = (JST0_TV a ("Member " ++ show m))
  a0 = a + 1
  -- infer typen
  (a1,o ,gamma1,c_1) = cg_Expression (a0,gamma ) e1
  (a2,t2,gamma2,c_2) = cg_Expression (a1,gamma1) e2
  c = [SubType o (object_singleton NotRec m tm Definite),
       SubType t2 tm]
  in (a2,t2,gamma2,concat [c_1,c_2,c])

cg_TmemX :: Con_in -> ([JSNode],String,[[JSNode]]) -> Con_out
cg_TmemX (_a,_gamma) (_e,_m,_ei) | trace 10 ("TmemX") False = undefined
cg_TmemX (a,gamma) (e,m,ei) = let
  -- aquire new variables
  f = (ex_code_list e) ++ m -- get identifier for the function
  g = (JST0_TV a f)
  o = (JST0_TV (a+1) (f ++ "_memX_This"))
  tp = (JST0_TV (a+2) (f ++ "_memX_Ret"))
  a0 = a+3
  (a1,tx) = cg_ArgList_copy a0 ei 1 f

  -- infer function type
  (a2,te,gamma1,c_e) = cg_Expression (a1,gamma) e
  c_te = [SubType te (object_singleton NotRec m g Definite)]
  c_f  = [SubType g (JST0_Function o tx tp)]
  
  -- infer argument types
  (a3,ti,gamma2,c_ei) = cg_Exp_list (a2,gamma1) ei

  c = [SubType te o]
  c_arg = makeSubtype_list ti tx

  in (a3,tp,gamma2,concat[c,c_te,c_e,c_f,c_ei,c_arg])

cg_TfunX :: Con_in -> ([JSNode],[[JSNode]]) -> Con_out
cg_TfunX (_a,_gamma) (f,_ei) |trace 10 ("TfunX " ++ (show f)) False = undefined
cg_TfunX (a,gamma) (f,ei) = let
  -- get function ID
  fid = "[" ++ (ex_fID f) ++ "]"
  -- acquire new Variables
  o = (JST0_TV a (fid++"_funX_This"))
  tp = (JST0_TV (a+1) (fid++"_funX_Ret"))
  a0 = a+2
  (a2,tx) = cg_ArgList_copy a0 ei 1 fid
  
  -- infer function type
  (a3,g ,gamma2,c_g ) = cg_Expression      (a2,gamma ) f
  -- infer argument types
  (a4,ti,gamma4,c_ei) = cg_Exp_list (a3,gamma2) ei
  c_f  = [SubType g (JST0_Function o tx tp)]

  c = [Empty o]
  c_arg = makeSubtype_list ti tx
  in (a4,tp,gamma4,concat[c,c_ei,c_arg,c_f,c_g])

cg_Tcond :: Con_in -> (JSNode,JSNode,JSNode) -> Con_out
cg_Tcond (_a,_gamma) (_e1,_e2,_e3) | trace 10 ("Tcond") False = undefined
cg_Tcond (a,gamma) (e1,e2,e3) = let
  -- create new variables
  t = (JST0_TV a "Merge of if branches")
  a0 = a+1
  -- infer type
  (a1,tb,gamma1,c_1) = cg_Statement (a0,gamma ) e1
  (a2,tt,gammat,c_2) = cg_Statement (a1,gamma1) e2
  (a3,tf,gammaf,c_3) = cg_Statement (a2,gamma1) e3
  (c_G,gammar,a4) = context_min_constrain gammat gammaf a3
  c = [SubType tb JST0_Bool,
       SubType tf t,
       SubType tt t
      ]
  in (a4,t,gammar,concat [c,c_1,c_2,c_3,c_G])

cg_TvarD :: Con_in -> (String,[JSNode]) -> Con_out
cg_TvarD (_a,_gamma) (var,_e) | trace 10 ("TvarD " ++ var) False = undefined
cg_TvarD (a,gamma) (_var,e) = let
  (a1,t1,gamma1,c_1) = cg_Expression (a,gamma) e
  in (a1,JST0_None,gamma1,c_1)

cg_funExpr :: Con_in -> (String,[String],JSNode) -> Con_out
cg_funExpr (a,_gamma) (f,xi,_e) | trace 10 ("(" ++ show a ++ ")" ++ "FunExpr " ++ f ++ "(" ++ show xi ++ ")") False = undefined
cg_funExpr (a,gamma) (f,xi,e) = let
  -- define variables
  tThis = JST0_TV a (f ++ "_funD_This")
  txp = JST0_TV (a+1) (f ++ "_funD_Ret")
  a0 = a+2
  (a1,tx) = cg_ArgList a0 xi
  -- prepare contexts
  tf = JST0_Function tThis tx txp -- New function, Fun Exprs are not evaluated in the 1st pass
  gammap | f == "" = gamma
         | otherwise = var_set gamma f (tf,Definite)
  gammaf0 = var_set_list gammap ("this":xi) (list2Def (tThis:tx))
  -- Do a full 3 pass parse
  (a2,gammaf1)   = p1_Statement (a1,gammaf0) e
  (a3,gammaf2)   = p2_Statement (a2,gammaf1) e
  (a4,te,_g1,ce) = cg_Statement (a3,gammaf2) e
  
  tep = case te of
    (JST0_Ret tr) -> tr
    _ -> JST0_None
    --TODO insert type void here
  c = [SubType txp tep,SubType tep txp, IsObject tThis]
  -- TODO create EQUAL type constraint
  in (a4,tf,gammap,concat[c,ce])

cg_funStmt :: Con_in -> (String,[String],JSNode) -> Con_out
cg_funStmt (_a,_gamma) (f,xi,_e) | trace 10 ("Tfund " ++ f ++ "(" ++ show xi ++ ")") False = undefined
cg_funStmt (a,gamma) (f,xi,e) = let
    -- define variables
    tThis = JST0_TV a (f ++ "_funD_This")
    a0 = a+1
    (a1,tx) = cg_ArgList a0 xi
    -- prepare contexts
    (tf,Definite) = var_get gamma f -- function type has been defined definite in pass 1, otherwise something went wrong horribly
    gammaf0 = var_set_list gamma ("this":xi) (list2Def (tThis:tx))
    -- Do a full 3 pass parse
    (a2,gammaf1)   = p1_Statement (a1,gammaf0) e
    (a3,gammaf2)   = p2_Statement (a2,gammaf1) e
    (a4,te,_g1,ce) = cg_Statement (a3,gammaf2) e
    txp = case te of
      (JST0_Ret tep) -> tep   
      _ -> JST0_None  --TODO: this should be void
    -- put together result
    c = [SubType tf (JST0_Function tThis tx txp), IsObject tThis]
    in (a4,tf,gamma,concat[c,ce])

cg_TobjLit :: Con_in -> [(String,[JSNode])] -> Con_out
cg_TobjLit (_a,_gamma1) _fields | trace 10 ("TObjD") False = undefined
cg_TobjLit (a,gamma1) fields = let
  -- create TVs
  o = JST0_TV a "objLit"
  a0 = a+1
  -- infer type
  (ap,types,gammakp1,c1) = cg_fields (a0,gamma1) fields
  to = object_from_list NotRec types
  c = [SubType o to,
       Only_type o to]
  in (ap,o,gammakp1,concat [c,c1])

cg_Twhile :: Con_in -> (JSNode,JSNode) -> Con_out
cg_Twhile (_a,_gamma) (_bool,_e) | trace 10 ("Twhile") False = undefined
cg_Twhile (a,gamma) (bool,e) = let
  (a1, tb, gamma1,c_1) = cg_Statement (a ,gamma ) bool
  (a2,_te,_gamma2,c_2) = cg_Statement (a1,gamma1) e
  c = [SubType tb JST0_Bool]
  in (a2,JST0_None,gamma1,concat [c,c_1,c_2])

cg_Tfor :: Con_in -> ([JSNode],JSNode,JSNode,JSNode) -> Con_out
cg_Tfor (_a,_gamma) (_e1,_e2,_e3,_body) | trace 10 ("Tfor") False = undefined
cg_Tfor (a,gamma) (e1,e2,e3,body) = let
  (a1,t1,gamma1,c_1) = cg_Stmt_mult (a ,gamma ) e1
  (a2,t2,gamma2,c_2) = cg_Statement (a1,gamma1) e2
  (a3,t3,gamma3,c_3) = cg_Stmt_mult (a2,gamma2) [body,e3]
  in (a3,JST0_None,gamma2,concat [c_1,c_2,c_3])

cg_OPPlus :: Con_in -> ([JSNode],[JSNode]) -> Con_out
cg_OPPlus (_a,_gamma) (_js1,js2) | trace 10 ("OP+") False = undefined
cg_OPPlus (a,gamma) (e1,e2) = let
  t =JST0_TV a "Result +"
  a0 = a+1
  (a1,t1,gamma1,c_1) = cg_Expression (a0,gamma ) e1
  (a2,t2,gamma2,c_2) = cg_Expression (a1,gamma1) e2
  c = [Cast t t1,Cast t t2]
  in (a2,t,gamma2,concat [c_1,c_2,c])

cg_OPComparison :: Con_in -> ([JSNode],[JSNode]) -> Con_out
cg_OPComparison (_a,_gamma) (_js1,_js2) | trace 10 ("OPComparison") False = undefined
cg_OPComparison (a,gamma) (js1,js2) = let
  (a1,t1,gamma1,c_1) = cg_Expression (a,gamma) js1
  (a2,t2,gamma2,c_2) = cg_Expression (a1,gamma1) js2
  c = [] --[SubType t1 t2,SubType t2 t1] JavaScript allows to compare all sort of different values
  in (a2,JST0_Bool,gamma2,concat[c_1,c_2,c])

cg_OPArithmetic :: Con_in -> ([JSNode],[JSNode]) -> Con_out
cg_OPArithmetic (_a,_gamma) (_js1,_js2) | trace 10 ("OPArithmetic") False = undefined
cg_OPArithmetic (a,gamma) (js1,js2) = let
  (a1,t1,gamma1,c_1) = cg_Expression (a ,gamma ) js1
  (a2,t2,gamma2,c_2) = cg_Expression (a1,gamma1) js2
  c = [ SubType t1 JST0_Int,
        SubType t2 JST0_Int]
  in (a2,JST0_Int,gamma2,concat[c_1,c_2,c])

cg_OPLogic :: Con_in -> ([JSNode],[JSNode]) -> Con_out
cg_OPLogic (_a,_gamma) (_js1,_js2) | trace 10 ("OPLogic") False = undefined
cg_OPLogic (a,gamma) (js1,js2) = let
  t = JST0_TV a ("Result LOp")
  a0 = a+1
  (a1,t1,gamma1,c_1) = cg_Expression (a0,gamma ) js1
  (a2,t2,gamma2,c_2) = cg_Expression (a1,gamma1) js2
  c = [ SubType t1 t,
        SubType t2 t]
  in (a2,t,gamma2,concat[c_1,c_2,c])

cg_OPBang :: Con_in -> [JSNode] -> Con_out
cg_OPBang (_a,_gamma) js  | trace 10 ("OP!") False = undefined
cg_OPBang (a,gamma) js = let
  (a1,t1,gamma1,c_1) = cg_Expression (a,gamma) js
  c = [Cast JST0_Bool t1]
  in (a1,JST0_Bool,gamma1,concat [c,c_1])

cg_OPSign :: Con_in -> [JSNode] -> Con_out
cg_OPSign (_a,_gamma) js  | trace 10 ("OP+-") False = undefined
cg_OPSign (a,gamma) js = let
  (a1,t1,gamma1,c_1) = cg_Expression (a,gamma) js
  c = [SubType JST0_Int t1]
  in (a1,JST0_Int,gamma1,concat [c,c_1])

cg_OPIntPF :: Con_in -> [JSNode] -> Con_out
cg_OPIntPF (_a,_gamma) js  | trace 10 ("OP++--") False = undefined
cg_OPIntPF (a,gamma) js = let
  (a1,t1,gamma1,c_1) = cg_Expression (a,gamma) js
  c = [SubType JST0_Int t1]
  in (a1,JST0_Int,gamma1,concat [c,c_1])

cg_OPCond :: Con_in -> ([[JSNode]] ,[[JSNode]],[[JSNode]]) -> Con_out
cg_OPCond (a,gamma) (cond,true,false) = let
  t = JST0_TV a ("Result OP?")
  a0 = a+1
  (a1,tb,gamma1,c_b) = cg_Exp_mult (a0,gamma ) cond
  (a2,tt,gammat,c_t) = cg_Exp_mult (a1,gamma1) true
  (a3,tf,gammaf,c_f) = cg_Exp_mult (a2,gamma1) false
  (c_G,gammar,a4) = context_min_constrain gammat gammaf a3
  c = [SubType tt t,
       SubType tf t,
       Cast JST0_Bool tb]
  in (a4,t,gammar,concat[c_b,c_f,c_t,c_G,c])

cg_TstringLit :: Con_in -> String -> Con_out
cg_TstringLit (_a,_gamma) s | trace 10 ("StringD: " ++ s) False = undefined
cg_TstringLit (a,gamma) _s =
  (a,JST0_String "",gamma,[])

cg_Treturn :: Con_in -> [[JSNode]] -> Con_out
cg_Treturn (_a,_gamma) _js | trace 10 ("Return: ") False = undefined
cg_Treturn (a,gamma) js = let
  (ap,t,gp,cp) = cg_Exp_mult (a,gamma) js
  in (ap,JST0_Ret t,gp,cp)
                            
----------------------------------------
-- Auxiliary Functions
----------------------------------------
list2Def :: [Type] -> [(Type,FieldType)]
list2Def = Prelude.map (\t -> (t,Definite))

cg_fields :: Con_in -> [(String,[JSNode])] -> (Int,[(String,Type)],Context,[Constrain])
cg_fields (a,gamma) js | trace 10 "fields" False = undefined
cg_fields (a,gamma) [] = (a,[],gamma,[])
cg_fields (a,gamma) ((s,js):jx) = let
  (as,ts,gammas,c_s) = cg_Expression (a,gamma) js
  (ax,l ,gammax,c_x) = cg_fields (as,gammas) jx
  in (ax,(s,ts):l,gammax,concat[c_s,c_x])

cg_ArgList :: Int -> [String] -> (Int,[Type])
cg_ArgList a xs | trace 10 "cg_ArgList" False = undefined
cg_ArgList a [] = (a,[])
cg_ArgList a (x:xs) = let
  tx = JST0_TV a x
  (as,txs) = cg_ArgList (a+1) xs
  in (as,tx:txs)

cg_ArgList_copy :: Int -> [a] -> Int -> String -> (Int,[Type])
cg_ArgList_copy a xs _i _f | trace 10 "ArgList_copy" False = undefined
cg_ArgList_copy a [] _i _f = (a,[])
cg_ArgList_copy a (_x:xs) i f= let
  tx = JST0_TV a (f ++ " Argument" ++ show i)
  (as,txs) = cg_ArgList_copy (a+1) xs (i+1) f
  in (as,tx:txs)


----------------------------------------
-- Pass 2:
--   add all veriable declarations to the context
-- TODO:
--   infer literal types of variable initialisations directly
----------------------------------------

type P2_in = (Int,Context)
type P2_out = (Int,Context)

p2_Statement :: P2_in -> JSNode -> P2_out
p2_Statement (_a,_gamma) j | trace 10 ("p2_JSNode : " ++ (show j)) False = undefined
p2_Statement (a,gamma) (NT n _l _c) = p2_Statement (a,gamma) (NN n)
p2_Statement (a,gamma) (NN n)
  -- boxes
  | is_SourceElementsTop_JS (NN n) = p2_Stmt_mult (a,gamma) (ex_SourceElementsTop n)
  | is_Variables_JS         (NN n) = p2_Stmt_mult (a,gamma) (ex_Variables         n)
  | is_Block_JS             (NN n) = p2_Stmt_mult (a,gamma) (ex_Block             n)
  | is_Expression_JS        (NN n) = p2_Exp_Stmt  (a,gamma) (ex_Expression        n)
  | is_ExpressionParen_JS   (NN n) = p2_Exp_Stmt  (a,gamma) (ex_ExpressionParen   n)

  -- unneccessary
  | is_emptyLiteral_JS (NN n) = (a,gamma)
  | is_semicolon_JS    (NN n) = (a,gamma)
                                
  -- handled language features
  | is_Tcond_JS   (NN n) = p2_Tcond   (a,gamma) (ex_Tcond    (NN n))
  | is_funStmt_JS (NN n) = p2_funStmt (a,gamma) (ex_TfunStmt (NN n))
  | is_TvarD_JS   (NN n) = p2_TvarD   (a,gamma) (ex_TvarD    (NN n))
  | is_Twhile_JS  (NN n) = p2_Twhile  (a,gamma) (ex_Twhile   (NN n))
  | is_Tfor_JS    (NN n) = p2_Tfor    (a,gamma) (ex_Tfor     (NN n))
  | is_Treturn_JS (NN n) = p2_Treturn (a,gamma) (ex_Treturn  (NN n))
p2_Statement (a,gamma) j | trace 1 ("p2: Expression not handled" ++ show j) True = (a,gamma)
                         | True = undefined

p2_Stmt_mult :: P2_in -> [JSNode] -> P2_out
p2_Stmt_mult (a,gamma) js | trace 10 "p2_Stmt_mult" False  = undefined
p2_Stmt_mult (a,gamma) [] = (a,gamma)
p2_Stmt_mult (a,gamma) [j] = p2_Statement (a,gamma) j
p2_Stmt_mult (a,gamma) (j:js) = let
  (a1,gamma1) = p2_Statement (a ,gamma ) j
  (a2,gamma2) = p2_Stmt_mult (a1,gamma1) js
  in (a2,gamma2)

p2_Exp_Stmt :: P2_in -> [[JSNode]] -> P2_out
p2_Exp_Stmt = p2_Exp_mult

p2_Expression :: P2_in -> [JSNode] -> P2_out
p2_Expression (a,gamma) js_dirty = let
  js = filter_irrelevant js_dirty
  res   
    | is_Tnull_JS js      =               (a,gamma)
    | is_Tint_JS js       =               (a,gamma)
    | is_TboolLit_JS js   = p2_TboolLit   (a,gamma)
    | is_TstringLit_JS js = p2_TstringLit (a,gamma) (ex_TstringLit js)
    | is_TobjLit_JS js    = p2_TobjLit    (a,gamma) (ex_TobjLit    js)

    | is_TvarR_JS js  =           (a,gamma)
    | is_TvarW_JS js  = p2_TvarW  (a,gamma) (ex_TvarW  js)
    | is_TmemR_JS js  = p2_TmemR  (a,gamma) (ex_TmemR  js)
    | is_TmemW1_JS js = p2_TmemW1 (a,gamma) (ex_TmemW1 js)
    | is_TmemW2_JS js = p2_TmemW2 (a,gamma) (ex_TmemW2 js)
    | is_TmemX_JS js  = p2_TmemX  (a,gamma) (ex_TmemX  js)
    | is_TfunX_JS js  = p2_TfunX  (a,gamma) (ex_TfunX  js)
    | is_TnewX_JS js  = p2_TfunX  (a,gamma) (ex_TnewX  js)

    | is_funExpr_JS js = p2_funExpr (a,gamma) (ex_TfunExpr js)

    | is_OPPlus_JS       js = p2_OPPlus       (a,gamma) (ex_BinOp js)
    | is_OPArithmetic_JS js = p2_OPArithmetic (a,gamma) (ex_BinOp js)
    | is_OPComparison_JS js = p2_OPComparison (a,gamma) (ex_BinOp js)
    | is_OPLogic_JS      js = p2_OPLogic      (a,gamma) (ex_BinOp js)
    | is_OPBang_JS       js = p2_OPBang       (a,gamma) (ex_UnOp  js)
    | is_OPSign_JS       js = p2_OPSign       (a,gamma) (ex_UnOp  js)
    | is_OPCond_JS       js = p2_OPCond       (a,gamma) (ex_TerOp js)
    | is_OPIntPostfix_JS js = p2_OPIntPF      (a,gamma) (ex_PostfixOp  js)

    | is_Statement_single js = p2_Stmt_mult (a,gamma) js
    | js == [] = (a,gamma)
  in res

p2_Exp_mult :: P2_in -> [[JSNode]] -> P2_out
p2_Exp_mult (a,gamma) [] = (a,gamma)
p2_Exp_mult (a,gamma) [j] = p2_Expression (a,gamma) j
p2_Exp_mult (a,gamma) (j:js) = let
  (a1,gamma1) = p2_Expression (a ,gamma ) j
  (a2,gamma2) = p2_Exp_mult   (a1,gamma1) js
  in (a2,gamma2)

p2_TvarW :: P2_in -> (String,[JSNode]) -> P2_out
p2_TvarW (a,gamma) (_x,e) = p2_Expression (a,gamma) e

p2_TmemR :: P2_in -> ([JSNode],String) -> P2_out
p2_TmemR (a,gamma) (e,_m) = p2_Expression (a,gamma) e

p2_TmemW1 :: P2_in -> (String,String,[JSNode]) -> P2_out
p2_TmemW1 (a,gamma) (_var,_m,e) = p2_Expression (a,gamma) e

p2_TmemW2 :: P2_in -> ([JSNode],String,[JSNode]) -> P2_out
p2_TmemW2 (a,gamma) (e1,_m,e2) = p2_Exp_mult (a,gamma) [e1,e2]

p2_TmemX :: P2_in -> ([JSNode],String,[[JSNode]]) -> P2_out
p2_TmemX (a,gamma) (e1,_m,ei) = p2_Exp_mult (a,gamma) (e1:ei)

p2_TfunX :: P2_in -> ([JSNode],[[JSNode]]) -> P2_out
p2_TfunX (a,gamma) (ef,ei) = p2_Exp_mult (a,gamma) (ef:ei)

p2_Tcond :: P2_in -> (JSNode,JSNode,JSNode) -> P2_out
p2_Tcond (a,gamma) (e1,e2,e3) = p2_Stmt_mult (a,gamma) [e1,e2,e3]

p2_TvarD :: P2_in -> (String,[JSNode]) -> P2_out
p2_TvarD (a,gamma) (var,e) = let 
  tvar = JST0_TV a (var ++ "Decl")
  gammap = var_set gamma var (tvar,Potential)
  in p2_Expression (a+1,gammap) e

-- var decls in function body are hidden from this scope
p2_funExpr :: P2_in -> (String,[String],JSNode) -> P2_out
p2_funExpr (a,gamma) (_f,_x,_e) = (a,gamma)

p2_funStmt :: P2_in -> (String,[String],JSNode) -> P2_out
p2_funStmt (a,gamma) (_f,_x,_e) = (a,gamma)

p2_TobjLit :: P2_in -> [(String,[JSNode])] -> P2_out
p2_TobjLit (a,gamma) [] = (a,gamma)
p2_TobjLit (a,gamma) ((_s,js):jx) = let
           (a1,gamma1) = p2_Expression (a,gamma) js
           in p2_TobjLit (a1,gamma1) jx

p2_Twhile :: P2_in -> (JSNode,JSNode) -> P2_out
p2_Twhile (a,gamma) (bool,s) = p2_Stmt_mult (a,gamma) [bool,s]

p2_Tfor :: P2_in -> ([JSNode],JSNode,JSNode,JSNode) -> P2_out
p2_Tfor (a,gamma) (e1,e2,e3,body) =p2_Stmt_mult (a,gamma) (body:e3:e2:e1)

p2_OPPlus :: P2_in -> ([JSNode],[JSNode]) -> P2_out
p2_OPPlus (a,gamma) (e1,e2) = p2_Exp_mult (a,gamma) [e1,e2]
 
p2_OPArithmetic:: P2_in -> ([JSNode],[JSNode]) -> P2_out
p2_OPArithmetic (a,gamma) (e1,e2) = p2_Exp_mult (a,gamma) [e1,e2]

p2_OPComparison :: P2_in -> ([JSNode],[JSNode]) -> P2_out
p2_OPComparison (a,gamma) (e1,e2) = p2_Exp_mult (a,gamma) [e1,e2]

p2_OPLogic :: P2_in -> ([JSNode],[JSNode]) -> P2_out
p2_OPLogic (a,gamma) (e1,e2) = p2_Exp_mult (a,gamma) [e1,e2]

p2_OPBang :: P2_in -> [JSNode] -> P2_out
p2_OPBang (a,gamma) e = p2_Expression (a,gamma) e

p2_OPSign :: P2_in -> [JSNode] -> P2_out
p2_OPSign (a,gamma) e = p2_Expression (a,gamma) e

p2_OPIntPF :: P2_in -> [JSNode] -> P2_out
p2_OPIntPF (a,gamma) e = p2_Expression (a,gamma) e

p2_OPCond :: P2_in -> ([[JSNode]],[[JSNode]],[[JSNode]]) -> P2_out
p2_OPCond (a,gamma) (cond,true,false) = p2_Exp_mult (a,gamma) (concat [cond,true,false])

p2_TstringLit :: P2_in -> String -> P2_out
p2_TstringLit (a,gamma) _s = (a,gamma)

p2_TboolLit :: P2_in -> P2_out
p2_TboolLit (a,gamma) = (a,gamma)

p2_Treturn :: P2_in -> [[JSNode]] -> P2_out
p2_Treturn (a,gamma) js = p2_Exp_mult (a,gamma) js

----------------------------------------
-- Function for Pass 1:
--  add all function declarations to the context
----------------------------------------
type P1_in = (Int,Context)
type P1_out = (Int,Context)

p1_Statement :: P1_in -> JSNode -> P1_out
p1_Statement (_a,_gamma) j | trace 10 ("p1_JSNode : " ++ (show j)) False = undefined
p1_Statement (a,gamma) (NT n _l _c) = p1_Statement (a,gamma) (NN n)
p1_Statement (a,gamma) (NN n)
  -- boxes
  | is_SourceElementsTop_JS (NN n) = p1_Stmt_mult (a,gamma) (ex_SourceElementsTop n)
  | is_Variables_JS         (NN n) = p1_Stmt_mult (a,gamma) (ex_Variables         n)
  | is_Block_JS             (NN n) = p1_Stmt_mult (a,gamma) (ex_Block             n)
  | is_Expression_JS        (NN n) = p1_Exp_Stmt  (a,gamma) (ex_Expression        n)
  | is_ExpressionParen_JS   (NN n) = p1_Exp_Stmt  (a,gamma) (ex_ExpressionParen   n)

  -- unneccessary
  | is_emptyLiteral_JS (NN n) = (a,gamma)
  | is_semicolon_JS    (NN n) = (a,gamma)
                                
  -- handled language features
  | is_Tcond_JS   (NN n) = p1_Tcond   (a,gamma) (ex_Tcond    (NN n))
  | is_funStmt_JS (NN n) = p1_funStmt (a,gamma) (ex_TfunStmt (NN n))
  | is_TvarD_JS   (NN n) = p1_TvarD   (a,gamma) (ex_TvarD    (NN n))
  | is_Twhile_JS  (NN n) = p1_Twhile  (a,gamma) (ex_Twhile   (NN n))
  | is_Tfor_JS    (NN n) = p1_Tfor    (a,gamma) (ex_Tfor     (NN n))
  | is_Treturn_JS (NN n) = p1_Treturn (a,gamma) (ex_Treturn  (NN n))
p1_Statement (a,gamma) j | error ("P1: Statement not handled" ++ show j) = (a,gamma)
                         | True = undefined

p1_Stmt_mult :: P1_in -> [JSNode] -> P1_out
p1_Stmt_mult (a,gamma) [] = (a,gamma)
p1_Stmt_mult (a,gamma) [j] = p1_Statement (a,gamma) j
p1_Stmt_mult (a,gamma) (j:js) = let
  (a1,gamma1) = p1_Statement (a ,gamma ) j
  (a2,gamma2) = p1_Stmt_mult (a1,gamma1) js
  in (a2,gamma2)

p1_Exp_Stmt :: P1_in -> [[JSNode]] -> P1_out
p1_Exp_Stmt = p1_Exp_mult

p1_Expression :: P1_in -> [JSNode] -> P1_out
p1_Expression (a,gamma) js_dirty = let
  js = filter_irrelevant js_dirty
  res 
    | is_Tnull_JS      js =               (a,gamma)
    | is_Tint_JS       js =               (a,gamma)
    | is_TboolLit_JS   js = p1_TboolLit   (a,gamma)
    | is_TstringLit_JS js = p1_TstringLit (a,gamma) (ex_TstringLit js)
    | is_TobjLit_JS    js = p1_TobjLit    (a,gamma) (ex_TobjLit    js)

    | is_TvarR_JS  js =           (a,gamma)
    | is_TvarW_JS  js = p1_TvarW  (a,gamma) (ex_TvarW  js)
    | is_TmemR_JS  js = p1_TmemR  (a,gamma) (ex_TmemR  js)
    | is_TmemW1_JS js = p1_TmemW1 (a,gamma) (ex_TmemW1 js)
    | is_TmemW2_JS js = p1_TmemW2 (a,gamma) (ex_TmemW2 js)
    | is_TmemX_JS  js = p1_TmemX  (a,gamma) (ex_TmemX  js)
    | is_TfunX_JS  js = p1_TfunX  (a,gamma) (ex_TfunX  js)
    | is_TnewX_JS  js = p1_TfunX  (a,gamma) (ex_TnewX  js)

    | is_funExpr_JS js = p1_funExpr (a,gamma) (ex_TfunExpr js)

    | is_OPPlus_JS       js = p1_OPPlus       (a,gamma) (ex_BinOp js)
    | is_OPArithmetic_JS js = p1_OPArithmetic (a,gamma) (ex_BinOp js)
    | is_OPComparison_JS js = p1_OPComparison (a,gamma) (ex_BinOp js)
    | is_OPLogic_JS      js = p1_OPLogic      (a,gamma) (ex_BinOp js)
    | is_OPBang_JS       js = p1_OPBang       (a,gamma) (ex_UnOp  js)
    | is_OPSign_JS       js = p1_OPSign       (a,gamma) (ex_UnOp  js)
    | is_OPCond_JS       js = p1_OPCond       (a,gamma) (ex_TerOp js)
    | is_OPIntPostfix_JS js = p1_OPIntPF      (a,gamma) (ex_PostfixOp  js)

    | is_Statement_single js = p1_Stmt_mult (a,gamma) js
    | js == [] = (a,gamma)
  in res

p1_Exp_mult :: P1_in -> [[JSNode]] -> P1_out
p1_Exp_mult (a,gamma) [] = (a,gamma)
p1_Exp_mult (a,gamma) [j] = p1_Expression (a,gamma) j
p1_Exp_mult (a,gamma) (j:js) = let
  (a1,gamma1) = p1_Expression (a ,gamma ) j
  (a2,gamma2) = p1_Exp_mult   (a1,gamma1) js
  in (a2,gamma2)

p1_TvarW :: P1_in -> (String,[JSNode]) -> P1_out
p1_TvarW (a,gamma) (_x,e) = p1_Expression (a,gamma) e

p1_TmemR :: P1_in -> ([JSNode],String) -> P1_out
p1_TmemR (a,gamma) (e,_m) = p1_Expression (a,gamma) e

p1_TmemW1 :: P1_in -> (String,String,[JSNode]) -> P1_out
p1_TmemW1 (a,gamma) (_var,_m,e) = p1_Expression (a,gamma) e

p1_TmemW2 :: P1_in -> ([JSNode],String,[JSNode]) -> P1_out
p1_TmemW2 (a,gamma) (e1,_m,e2) = p1_Exp_mult (a,gamma) [e1,e2]

p1_TmemX :: P1_in -> ([JSNode],String,[[JSNode]]) -> P1_out
p1_TmemX (a,gamma) (e1,_m,ei) = p1_Exp_mult (a,gamma) (e1:ei)

p1_TfunX :: P1_in -> ([JSNode],[[JSNode]]) -> P1_out
p1_TfunX (a,gamma) (ef,ei) = p1_Exp_mult (a,gamma) (ef:ei)

p1_Tcond :: P1_in -> (JSNode,JSNode,JSNode) -> P1_out
p1_Tcond (a,gamma) (e1,e2,e3) = p1_Stmt_mult (a,gamma) [e1,e2,e3]

p1_TvarD :: P1_in -> (String,[JSNode]) -> P1_out
p1_TvarD (a,gamma) (_var,e) = p1_Expression (a,gamma) e

-- ignore function expressions:
--  - the body is hidden from the outer scope
--  - the function itself only gets defined in the main execution
p1_funExpr :: P1_in -> (String,[String],JSNode) -> P1_out
p1_funExpr (a,gamma) (f,_x,e) = (a,gamma)

-- ignore function body, but function name is defined here
p1_funStmt :: P1_in -> (String,[String],JSNode) -> P1_out
p1_funStmt (a,gamma) (f,_x,e) = let
  tf = JST0_TV a (f ++ "Decl")
  gammap = var_set gamma f (tf,Definite)
  in (a+1,gammap)

p1_TobjLit :: P1_in -> [(String,[JSNode])] -> P1_out
p1_TobjLit (a,gamma) [] = (a,gamma)
p1_TobjLit (a,gamma) ((_s,js):jx) = let
           (a1,gamma1) = p1_Expression (a,gamma) js
           in p1_TobjLit (a1,gamma1) jx

p1_Twhile :: P1_in -> (JSNode,JSNode) -> P1_out
p1_Twhile (a,gamma) (bool,s) = p1_Stmt_mult (a,gamma) [bool,s]

p1_Tfor :: P1_in -> ([JSNode], JSNode, JSNode, JSNode) -> P1_out
p1_Tfor (a,gamma) (e1,e2,e3,body) = p1_Stmt_mult (a,gamma) (e2:e3:body:e1)

p1_OPPlus :: P1_in -> ([JSNode],[JSNode]) -> P1_out
p1_OPPlus (a,gamma) (e1,e2) = p1_Exp_mult (a,gamma) [e1,e2]
 
p1_OPArithmetic:: P1_in -> ([JSNode],[JSNode]) -> P1_out
p1_OPArithmetic (a,gamma) (e1,e2) = p1_Exp_mult (a,gamma) [e1,e2]

p1_OPComparison :: P1_in -> ([JSNode],[JSNode]) -> P1_out
p1_OPComparison (a,gamma) (e1,e2) = p1_Exp_mult (a,gamma) [e1,e2]

p1_OPLogic :: P1_in -> ([JSNode],[JSNode]) -> P1_out
p1_OPLogic (a,gamma) (e1,e2) = p1_Exp_mult (a,gamma) [e1,e2]

p1_OPBang :: P1_in -> [JSNode] -> P1_out
p1_OPBang = p1_Expression

p1_OPSign :: P1_in -> [JSNode] -> P1_out
p1_OPSign = p1_Expression

p1_OPIntPF :: P1_in -> [JSNode] -> P1_out
p1_OPIntPF = p1_Expression

p1_OPCond :: P1_in -> ([[JSNode]],[[JSNode]],[[JSNode]]) -> P1_out
p1_OPCond (a,gamma) (cond,true,false) = p1_Exp_mult (a,gamma) (concat [cond,true,false])

p1_TstringLit :: P1_in -> String -> P1_out
p1_TstringLit (a,gamma) _s = (a,gamma)

p1_TboolLit :: P1_in -> P1_out
p1_TboolLit (a,gamma) = (a,gamma)

p1_Treturn :: P1_in -> [[JSNode]] -> P1_out
p1_Treturn (a,gamma) js = p1_Exp_mult (a,gamma) js

