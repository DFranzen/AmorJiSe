module AnnotGen (
  annotConstGen,
) where

import Language.JavaScript.Parser.AST
--import Language.JavaScript.Parser.SrcLocation
import JST0P_types
import JST0_type_aux
import JST0P_context
import JST0P_constrain
import JST0P_solution

import Debugging

import Conditionals
import Extraction

import Res_model




----------------------------------------
-- Input/Output types
----------------------------------------
-- next index for TV
-- next index for annotation
-- (type)
-- Type context
-- Annotation
-- (Constraints)
----------------------------------------
type Con_in =  (Int, Int,         ContextAn, [Annotation], SolutionAn)
type Con_out = (Int, Int, TypeAn, ContextAn, [Annotation], [ConstrainAn])

----------------------------------------
-- Sum of annotations,
-- first is positive 
-- second in negative
----------------------------------------
type Annotation_sum = ([Annotation],[Annotation])


----------------------------------------
-- Generate constraints from parsed JavaScript
----------------------------------------
-- Input:
--   - Next free annotation TV index (used for the input annotation)
--   - Context (including the solution)
--   - Solution to the TVs
-- Return
--   - next free annotation TV index, needed since the context & solution already contains annotation variables
--   - Type+ of the whole Statement
--   - Resource Annotation of left-over
--   - Context after first pass
--   - Context after execution
--   - List of Constraint on the annotations
----------------------------------------
annotConstGen :: (Int,ContextAn,SolutionAn) -> JSNode -> (Int,TypeAn,[Annotation], ContextAn, ContextAn, [ConstrainAn])
annotConstGen (b,g,sol) j = let
  n0 = N b              -- New variable for the res at the start
  n0p = N (b+1)         -- New variable for the res at the end
  b0 = (b+2)
  a0 = 0
  (a1,b1,g1,n1) = pp1_Statement (a0,b0,sol,g ) j -- first pass: Functions
  (a2,b2,g2,n2) = pp2_Statement (a1,b1,sol,g1) j -- second: Variable Declerations
  (a3,b3,t3,g3,n3,c3) = ag_Statement (a2,b2,g2,[n0p],sol) j -- real pass
  c = (Eq [n0] [n0p,I n1,I n2]) -- n0 needs to suffice for all three passes
  in (b3,t3,n3,g1,g3,c:c3)

----------------------------------------
-- Generate constraints for single Statement
----------------------------------------
ag_Statement :: Con_in -> JSNode -> Con_out
ag_Statement _gamma j | trace 10 ("(  )Statement " ++ renderNodeToString j) False = undefined
ag_Statement gamma (NT n _l _c) = ag_Statement gamma (NN n)
ag_Statement gamma (NN n)
  -- boxes
  | is_SourceElementsTop_JS (NN n) = ag_Stmt_mult gamma (ex_SourceElementsTop n)
  | is_Variables_JS         (NN n) = ag_Stmt_mult gamma (ex_Variables         n)
  | is_Block_JS             (NN n) = ag_Stmt_mult gamma (ex_Block             n)
  | is_Expression_JS        (NN n) = ag_Exp_Stmt  gamma (ex_Expression        n)
  | is_ExpressionParen_JS   (NN n) = ag_Exp_Stmt  gamma (ex_ExpressionParen   n)

  -- unneccessary
  | is_emptyLiteral_JS (NN n) = ag_empty gamma
  | is_semicolon_JS    (NN n) = ag_empty gamma

  -- statements
  | is_TvarD_JS   (NN n) = ag_TvarD   gamma (ex_TvarD   (NN n))
  | is_Tcond_JS   (NN n) = ag_Tcond   gamma (ex_Tcond   (NN n))
--  | is_Twhile_JS  (NN n) = ag_Twhile  gamma (ex_Twhile  (NN n))
--  | is_Tfor_JS    (NN n) = ag_Tfor    gamma (ex_Tfor    (NN n))
  | is_Treturn_JS (NN n) = ag_Treturn gamma (ex_Treturn (NN n))

  | is_funStmt_JS (NN n) = ag_funStmt gamma (ex_TfunStmt (NN n))
ag_Statement (a,b,g,n,_sol) j | error ("AG: Not handled " ++ show j) = (a,b,(JST0P_None,I 0,I 0),g,n,[])
                              | otherwise = undefined


----------------------------------------
-- analyse multiple Statements after eachother. Expect that every element in the list contains a single statement
----------------------------------------
ag_Stmt_mult :: Con_in -> [JSNode] -> Con_out
ag_Stmt_mult (a,b,g,n,sol) [] = (a,b,(JST0P_None,I 0,I 0),g,n,[])
ag_Stmt_mult (a,b,g,n,sol) [j] = let
  (a1,b1,t,g1,n1,c_1) = ag_Statement (a,b,g,n,sol) j
  b2 |trace 10 ("----------> " ++ show n ++ " |- " ++ renderNodeToString j ++ " , " ++ show n1 ) True = (b1 + 1) -1
  in (a1,b2,t,g1,n1,c_1)
ag_Stmt_mult (a,b,g,n,sol) (j:js) | trace 10 ("(AG)TSeq(stmt): " ++ renderStmtSeqToString (j:js) ++ " -> " ++ (show c_seq)) True = let
  n0 = N b
  c_0 = [Eq [n0, I c_seq] n]
  b0 = b+1
  (a1,b1,t1,g1,n1,c_1) = ag_Statement (a ,b0,g ,[n0] ,sol) j
  (a2,b2,t2,g2,n2,c_2) | trace 10 ("----------> " ++ show [n0] ++ " |- " ++ renderNodeToString j ++ " , " ++ show n1) True = ag_Stmt_mult (a1,b1,g1,n1,sol) js
  (a3,   t3,      c_3) | trace 10 ("----------> " ++ show n ++ " |- " ++ renderStmtSeqToString (j:js) ++ " , " ++ show n2) True = seq_typeAn (a2,sol) t1 t2
  in (a3,b2,t3,g2,n2,concat [c_0,c_1,c_2,c_3])

----------------------------------------
-- Analyse an expression statement (list of expressions)
----------------------------------------
-- TODO: salvage resources from t1 to JST0P_None
ag_Exp_Stmt :: Con_in -> [[JSNode]] -> Con_out
ag_Exp_Stmt g jss |trace 10 ("(  )ExpStmt: " ++ renderExpSeqToString jss) False = undefined
ag_Exp_Stmt g js = let
  (a1,b1,t1,n1,g1,c1) = ag_Exp_mult g js
  in (a1,b1,(JST0P_None,I 0,I 0),n1,g1,c1)

----------------------------------------
-- Analyse single expression
----------------------------------------
ag_Expression :: Con_in -> [JSNode] -> Con_out
ag_Expression (a,b,g,n,sol) js | trace 10 ("(  )swap: " ++ renderExpressionToString js) False = undefined
ag_Expression (a,b,g,n,sol) js_dirty = let
  (ap,bp,(t,nut,nt),gp,np,cs) = ag_Expression_prime (a,b,g,n,sol) js_dirty
  r = N bp
  nut1 = N (bp+1)
--  np1 = N (bp+2)
  c = [
    Eq [nut1,r] [nut]
--    Eq [np1] (r:np),
--    Gt [nt] [r]
      ]
  in (ap,(bp+2),(t,nut1,nt),gp,(r:np),concat [cs,c])

ag_Expression_prime :: Con_in -> [JSNode] -> Con_out
ag_Expression_prime (a,b,g,n,sol) js | trace 10 ("(  )expression: " ++ renderExpressionToString js) False = undefined
ag_Expression_prime (a,b,g,n,sol) js_dirty = let
  js = filter_irrelevant js_dirty
  gamma = (a,b,g,n,sol)
  res
    | is_Expression_single_JS      js = ag_Exp_mult gamma (ex_Expression_single      js)
    | is_ExpressionParen_single_JS js = ag_Exp_mult gamma (ex_ExpressionParen_single js)

    | is_Tnull_JS      js = ag_Tnull      gamma
    | is_Tint_JS       js = ag_Tint       gamma
    | is_TboolLit_JS   js = ag_TboolLit   gamma
    | is_TstringLit_JS js = ag_TstringLit gamma (ex_TstringLit js)
    | is_TobjLit_JS    js = ag_TobjLit    gamma (ex_TobjLit    js)

    | is_TvarR_JS  js = ag_TvarR  gamma (ex_TvarR  js)
    | is_TvarW_JS  js = ag_TvarW  gamma (ex_TvarW  js)
    | is_TmemR_JS  js = ag_TmemR  gamma (ex_TmemR  js)
    | is_TmemW1_JS js = ag_TmemW1 gamma (ex_TmemW1 js)
    | is_TmemW2_JS js = ag_TmemW2 gamma (ex_TmemW2 js)
    | is_TmemX_JS  js = ag_TmemX  gamma (ex_TmemX  js)
    | is_TfunX_JS  js = ag_TfunX  gamma (ex_TfunX  js)
    | is_TnewX_JS  js = ag_TfunX  gamma (ex_TnewX  js)

    | is_funExpr_JS js = ag_funExpr gamma (ex_TfunExpr js)

    | is_OPPlus_JS       js = ag_OPPlus       gamma (ex_BinOp js)
    | is_OPArithmetic_JS js = ag_OPArithmetic gamma (ex_BinOp js)
    | is_OPComparison_JS js = ag_OPComparison gamma (ex_BinOp js)
    | is_OPLogic_JS      js = ag_OPLogic      gamma (ex_BinOp js)
    | is_OPBang_JS       js = ag_OPBang       gamma (ex_UnOp  js)
    | is_OPSign_JS       js = ag_OPSign       gamma (ex_UnOp  js)
    | is_OPCond_JS       js = ag_OPCond       gamma (ex_TerOp js)
    | is_OPIntPostfix_JS js = ag_OPIntPF      gamma (ex_PostfixOp  js)

    | js == [] = (a,b,(JST0P_None,I 0,I 0),g,n,[])
  in res

----------------------------------------
-- analyse multiple Expressions, executed after each other
-- Result is the type of the last expression
----------------------------------------
ag_Exp_mult :: Con_in -> [[JSNode]] -> Con_out
ag_Exp_mult (a,b,g,n,sol) [] = (a,b,(JST0P_None,I 0,I 0),g,n,[])
ag_Exp_mult (a,b,g,n,sol) [j] = ag_Expression (a,b,g,n,sol) j
ag_Exp_mult (a,b,g,n,sol) (j:js) | trace 10 ("(AG)TSeq(expr): " ++ renderExpSeqToString (j:js) ++ " -> " ++ show c_seq) True = let
  n0 = N b
  b0 = b+1
  c0 = [Eq [n0,I c_seq] n]
  -- analyse sub-expressions
  (a1,b1,t1,g1,n1,c_1) = ag_Expression (a ,b0,g ,[n0],sol) j
  (a2,b2,t2,g2,n2,c_2) = ag_Exp_mult   (a1,b1,g1, n1 ,sol) js
  in (a2,b2,t2,g2,n2,concat[c0,c_1,c_2])

----------------------------------------
-- Analyse a list of expression each by their own.
-- Result is a list of one type for each expression
----------------------------------------
ag_Exp_list :: Con_in -> [[JSNode]] ->(Int,Int,[TypeAn],ContextAn,[Annotation],[ConstrainAn])
ag_Exp_list (a,b,g,n,sol) jss | trace 10 ("(  )ExpList: " ++ renderExpressionListToString jss ) False = undefined
ag_Exp_list (a,b,g,n,sol) [] = (a,b,[],g,n,[])
ag_Exp_list (a,b,g,n,sol) (js:jss) = let
                   (a1,b1,t1,g1,n1,c1) = ag_Expression      (a ,b ,g ,n ,sol) js
                   (a2,b2,t2,g2,n2,c2) = ag_Exp_list (a1,b1,g1,n1,sol) jss
                   in (a2,b2,t1:t2,g2,n2,concat [c1,c2])


----------------------------------------
-- Rules for constraint generation
-- correspinding to the Rules in the Theory
----------------------------------------
ag_empty :: Con_in -> Con_out
ag_empty (a,b,g,n,sol) = (a,b,(JST0P_None,I 0,I 0),g,n,[])

ag_Tnull :: Con_in -> Con_out
ag_Tnull (a,b,g,n,sol) = let
  -- get solution for variables
  (o,nuo,no) = solutionAn_get sol a
  a0 = a + 1
  npost = N b
  b0 = b + 1
  -- We don't have to count the resources inside the null-type, since access to those results in a runtime error anyway, so there is no 
  -- evaluation for programs who try to access them. They have to be sufficient, though.
  co = makeSuff (o,nuo,no)
  in (a0,b0,(o,nuo,no),g,[npost],(Eq [npost,nuo] n):co)

ag_Tint :: Con_in -> Con_out
ag_Tint (a,b,g,n,sol) | trace 10 ("(AG)TInt -> " ++ show c_val) False = undefined
ag_Tint (a,b,g,n,_sol) = let
  n0 = N b
  b0 = b+1
  in (a,b0,(JST0P_Int,I 0,I 0),g,[n0],[Eq [n0,I c_val] n])

ag_TboolLit :: Con_in -> Con_out
ag_TboolLit (a,b,g,n,sol) | trace 10 ("(AG)TBool -> " ++ show c_val) False = undefined
ag_TboolLit (a,b,g,n,_sol) = let
  n0 = N b
  b0 = b+1
  in (a,b0,(JST0P_Bool,I 0,I 0),g,[n0],[Eq [n0,I c_val] n])

ag_TvarR :: Con_in -> String -> Con_out
ag_TvarR (a,b,g,n,sol) var | trace 10 ("(AG)TvarR: " ++ var ++ ": " ++ show (var_get g var) ++ " -> " ++ show (c_varR)) False = undefined
ag_TvarR (a,b,g,n,sol) var = let
  -- create new ResTV
  n0 = N b
  b0 = b+1
  c0 = [Eq [n0,I c_varR] n]
  -- get solutions to the TVs
  tvar1  = solutionAn_get sol a
  tvar2  = solutionAn_get sol (a+1)
  a0  = a+2
  -- infer type
  tvar  = var_get_definite g var
  g1  = var_set g var (tvar1,Definite)
  c_split  = makeSplit tvar tvar1 tvar2
  in (a0,b0,tvar2,g1,[n0],concat[c0,c_split])

ag_TvarW :: Con_in -> (String,[JSNode]) -> Con_out
ag_TvarW (a,b,g,n,sol) (x,e) | trace 10 ("(AG)TvarW: " ++ x ++ "=" ++ renderExpressionToString e ++ " -> " ++ show c_varW) False = undefined
ag_TvarW (a,b,g,n,sol) (x,e) = let
  -- create new ResTV
  ne = N b
  nxp = N (b+1)
  n0 = N (b+2)
  b0 = b+3
  c0 = [Eq [n0,I c_varW] n]
  -- get solutions to the TVs
  txasse = solutionAn_get sol a
  txp    = solutionAn_get sol (a+1)
  a0 = a + 2
  -- extract at least a bit of resources from x:
--  ((_tx,nux,nx),_psi) = var_get g x --could use those resources, if psi = definite
  -- infer types
  (a1,b1,te,g1,nep,c_1) = ag_Expression (a0,b0,g,[n0],sol) e
  (tx,_psi) = var_get g1 x
  gp = var_set g1 x (tx,Definite)
  -- constraints
  c_xe = makeSplit te txasse txp
  c_st = makeSubtype txp tx
  in (a1,b1,txasse,gp,nep,concat[c_1,c_st,c_xe,c0])

ag_TmemR :: Con_in -> ([JSNode],String) -> Con_out
ag_TmemR (a,b,g,n,sol) (e,m) | trace 10 ("(AG)TmemR: " ++ renderExpressionToString e ++ "." ++ m ++ " -> " ++ show (c_memR)) False = undefined
ag_TmemR (a,b,g,n,sol) (e,m) = let
  -- create new ResTV
  n0 = N b
  b0 = b+1
  c0 = [Eq [n0,I c_memR] n]
  a0 = a+1
  -- infer type
  (a1,b1,o,g1,n1,c_1) = ag_Expression (a0,b0,g,[n0],sol) e
  (t2,Definite) = objectAn_get o m
  in (a1,b1,t2,g1,n1,concat [c_1,c0])

ag_TmemW1 :: Con_in -> (String,String,[JSNode]) -> Con_out
ag_TmemW1 (a,b,g,n,sol) (var,m,e) | trace 10 ("(AG)TvarR: " ++ var ++ " -> " ++ show (c_varW)) False = undefined
ag_TmemW1 (a,b,g,n,sol) (var,m,e) = let
  -- create new ResTVs
  n2p = N (b+1)
  n0 = N (b+2)
  b0 = b+3
  -- get solutions to TVs
  txp    = solutionAn_get sol (a+1)
  txasse = solutionAn_get sol (a+2)
  a0 = a + 3
  -- infer type
  (a1,b1,te,g1,n1,c_1) = ag_Expression (a0,b0,g,[n0],sol) e
  tx = var_get_definite g1 var
  (tm,psi_m) = objectAn_get tx m
  g2 = var_set g1 var (txp,Definite)
  (tmp,psi_mp) = objectAn_get txp m  --psi_mp should be Definite, but underlying system does not guarantee that
  -- create constraints
  c_extm = makeExtend m txp tx
--  c_m = makeSubtype te tmp
  c_ass = makeEmpty txasse
  c_Nm  = makeEqual_n_n te tm 
  c_Nmp = makeEqual_n_n te tmp
  c_e = makeEqual_nu_n te te
  c_0 | trace 10 ("(AG)TmemW1: " ++ var ++ "." ++ m ++ renderExpressionToString e ++ " -> " ++  show (c_memW psi_m)) True = [Eq [n0,I (c_memW psi_m),I c_varR] n]
  in (a1,b1,te,g2,n1,concat [c_extm,c_ass,c_Nm,c_Nmp,c_e,c_0,c_1])

ag_TmemW2 :: Con_in -> ([JSNode],String,[JSNode]) -> Con_out
ag_TmemW2 (a,b,g,n,sol) (e1,m,e2) | trace 10 ("(AG)TmemW1: " ++ renderExpressionToString e1 ++ "." ++ m ++ renderExpressionToString e2 ++ " -> " ++  show (c_memW Definite)) False = undefined
ag_TmemW2 (a,b,g,n,sol) (e1,m,e2) = let
  -- create new ResTV
  n0 = N b
  b0 = b+1
  c0=[Eq [n0,I (c_memW Definite)] n]
  -- get solutions to TVs
  tasse = solutionAn_get sol (a)
  a0 = a+1
  -- infer type
  (a1,b1,o ,g1,n1,c_1) = ag_Expression (a0,b0,g ,[n0],sol) e1
  (a2,b2,t2,g2,n2,c_2) = ag_Expression (a1,b1,g1,n1,sol) e2
  (tm,Definite) = objectAn_get o m
  -- create constraints
  c_ass = makeEmpty tasse
  c_Nm  = makeEqual_n_n t2 tm 
  c_e = makeEqual_nu_n t2 t2
  in (a2,b2,t2,g2,n2,concat [c_ass,c_Nm,c_e,c0])

ag_TmemX :: Con_in -> ([JSNode],String,[[JSNode]]) -> Con_out
ag_TmemX (a,b,gamma,n,sol) (e,m,ei) = let
  -- aquire new annotation variables
  n1 = N b
  npost = N (b+1)
  a0 = a+3
  b0 = b+2
  a1 = ag_ArgList_copy a0 ei
  -- infer function type
  (a2,b2,te,g1,nep,c_e) = ag_Expression (a1,b0,gamma,n,sol) e
  (g,Definite) = objectAn_get te m
  ((JST0P_Function o tx nf tp nfp),I 0,I 0) = g
--  c_n1 = [Eq [n1] (nf:nep)] Don't know why I put this, but now it looks wrong
  -- infer argument type
  (a3,b3,ti,g2,n2,c_ei) = ag_Exp_list (a2,b2,g1,nep,sol) ei
  c =[Eq [npost,I c_funX,nf] (nfp:n2),
      Gt n2 [nf]]
  c_g = makeEqual_all g ((JST0P_Function o tx nf tp nfp),I 0,I 0)
  c_st = makeSubtype te o
  c_ti = makeSubtype_list ti tx
  in (a3,b3,tp,g2,[npost],concat[c,c_g,c_ti,c_st,c_e,c_ei])

ag_TfunX :: Con_in -> ([JSNode],[[JSNode]]) -> Con_out
ag_TfunX (a,b,gamma,n,sol) (f,ei) | trace 10 ("(AG)TfunX: " ++ renderExpressionToString f ++ "(" ++ renderExpressionListToString ei ++ ")") False = undefined
ag_TfunX (a,b,gamma,n,sol) (f,ei) = let
  -- get function ID
  fid | trace 2 "14" True = "[" ++ ex_fID f ++ "]"
  -- create new annotation variables
  ngp = N b
  n0 = N (b+1)
  npost = N (b+2)
  a0 = a+2
  a2 | trace 2 "11" True = ag_ArgList_copy a0 ei
  b2 = b+3
  c0 = [Eq [n0,I c_funX] n]
  --infer function type
  (a3,b3,g,g1,n1,c_g)   |trace 2 "12" True = ag_Expression      (a2,b2,gamma,[n0],sol) f
  -- infer argument types
  (a4,b4,ti,g2,n2,c_ei) | trace 2 "13" True = ag_Exp_list (a3,b3,g1   ,n1,sol) ei
  ((JST0P_Function o tx nf tp nfp),_,_) = g

  c = [ Gt n2 [nf],
        Eq [npost,nf] (nfp:n2)]
  c_o | trace 2 "15" True = makeEmpty o
  c_ti | trace 2 "16" True = makeSubtype_list ti tx
  in (a4,b4,tp,g2,[npost],concat[c0,c_ti,c_o,c_ei,c,c_g])


ag_Tcond :: Con_in -> ([[JSNode]],JSNode,JSNode) -> Con_out
ag_Tcond (a,b,g,n,sol) (e1,e2,e3) | trace 10 ("(AG)Tcond (" ++ show a ++"): if (" ++renderExpSeqToString e1 ++ ") " ++ renderNodeToString e2 ++ " else " ++ renderNodeToString e3 ++ " -> " ++ show c_cond) False = undefined
ag_Tcond (a,b,g,n,sol) (e1,e2,e3) = let
  -- create new variables
  n0 = N b
  npost = N (b+1)
  b0 = b + 2
  c0 = [Eq [n0,I c_cond] n]
  -- get solution for TVs
  a0 = a+1
  -- infer type
  (a1,b1,_tb,g1,n1p,c_1) = ag_Exp_mult (a0,b0 ,g ,[n0],sol) e1
  (a2,b2, tt,gt,n2p,c_2) = ag_Stmt_mult (a1,b1 ,g1,n1p ,sol) [e2]
  (a3,b3, tf,gf,n3p,c_3) = ag_Stmt_mult (a2,b2 ,g1,n1p ,sol) [e3]
  (a4,t,c_t)             = merge_typeAn (a3,sol) tt tf
  c  = [Gt n2p [npost],
        Gt n3p [npost]]
  (c_G,gammar,a5,b4) | trace 2 ("Contexts: \n-->: " ++ show gt ++ "\n-->: " ++ show gf) True = context_min_constrain gt gf (a4,b3)
  in (a5,b4,t,gammar,[npost],concat [c,c0,c_1,c_2,c_3,c_G,c_t])

ag_TvarD :: Con_in -> (String,[JSNode]) -> Con_out
ag_TvarD (a,b,g,n,sol) (var,e) | trace 10 ("(AG)TvarD: var " ++ " " ++ renderExpressionToString e) False = undefined
ag_TvarD (a,b,g,n,sol) (_var,e) = let
  -- TODO: need to make Gamma(var) sufficient
  (a1,b1,t1,g1,n1,c_1) = ag_Expression (a,b,g,n,sol) e
  in (a1,b1,(JST0P_None,I 0,I 0),g1,n1,c_1)

ag_funExpr :: Con_in -> (String,[String],JSNode) -> Con_out
ag_funExpr (a,b,gamma,n,sol) (f,xi,e) = let
  -- define variables
  ne = N(b)
  nf = N (b+1)
  nfp = N (b+2)
--  ns = N (b+3)
  np = N (b+3)
  b1 = b + 4
  -- get solutions for TVs
  tThis = solutionAn_get sol a
  txp = solutionAn_get sol (a+1)
  a0 = a+2
  (a1,tx,cx) = ag_ArgList a0 xi sol
  -- prepare contexts
  tf = (JST0P_Function tThis tx nf txp nfp,I 0,I 0)
  gammap | f == "" = gamma
         | otherwise = var_set gamma f (tf,Definite)
  gf0 = var_set_list gammap ("this":xi) (list2DefAn (tThis:tx))
  -- Do full 3 pass parse
  (a2,b2,gf1,ne1)       = pp1_Statement (a1,b1,sol,gf0)    e
  (a3,b3,gf2,ne2)       = pp2_Statement (a2,b2,sol,gf1)    e
  (a4,b4,te,_g1,nep,ce) = ag_Statement  (a3,b3,gf2,[ne],sol) e
  tep = case te of
    (JST0P_Ret tr,I 0,I 0) -> tr
    _ -> (JST0P_None,I 0,I 0) -- no return given
  -- put together results
  c_txp = makeEqual_all txp tep
  -- TODO: get make and Subtype consistent (MakeSubtype should do MakeEqual for functions
  -- TODO: Check makeEqual uses Equal constraint
  c = [Gt [nf] [ne,I ne1,I ne2],
       Gt nep [nfp],
       Gt n [np,I c_funD]]
  in (a4,b4,tf,gammap,[np],concat [c_txp,c,ce,cx])

ag_funStmt :: Con_in -> (String,[String],JSNode) -> Con_out
ag_funStmt (a,b,gamma,n,sol) (f,xi,e) | trace 10 ("(AG)FunStmt: function " ++ show f ++ "(" ++ show_list xi ++ ") " ++ renderNodeToString e ++ " -> " ++ show c_funD) False = undefined
-- c_funD Resources have been accounted for in the first pass pp1_funStmt
ag_funStmt (a,b,gamma,n,sol) (f,xi,e) = let
  -- define variables
  ne = N(b)
  nf = N (b+1)
  nfp = N (b+2)
  b0 = b + 3
  -- get solutions for TVs
  tThis = solutionAn_get sol a
  a0 = a+1
  (a1,tx,cx) = ag_ArgList a0 xi sol
  -- prepare contexts
  (tf,Definite) = var_get gamma f
  gf0 = var_set_list gamma ("this":xi) (list2DefAn (tThis:tx))
  -- infer function body
  (a2,b2,gf1,ne1)       = pp1_Statement (a1,b0,sol,gf0) e
  (a3,b3,gf2,ne2)       = pp2_Statement (a2,b2,sol,gf1) e
  (a4,b4,te,_g1,nep,ce) = ag_Stmt_mult  (a3,b3,gf2,[ne],sol) [e]
  txp = case te of
    (JST0P_Ret tep,_,_) -> tep
    _ -> (JST0P_None,I 0,I 0) --TODO this should be void
  -- put together results
  c_tf = makeEqual_all tf ((JST0P_Function tThis tx nf txp nfp),I 0,I 0)
  c | trace 10 (f ++ ":" ++ show tThis ++ "," ++ show tx ++ "," ++ show nf ++ "-> " ++ show txp ++ "," ++ show nfp) True = [Eq [nf] [ne,I ne1,I ne2],Gt nep [nfp]]
  in (a4,b4,(JST0P_None,I 0,I 0),gamma,n,concat [c_tf,c,ce,cx])


ag_TobjLit :: Con_in -> [(String,[JSNode])] -> Con_out
ag_TobjLit (a,b,g,n,sol) fields | trace 10 ("(AG)TObjLit: " ++ show_fields fields ++ " -> " ++ show c_objD) False = undefined
ag_TobjLit (a,b,g,n,sol) fields = let
 -- create TVs
  no = N b
  n0 = N (b+1)
  b0 = b+2

  c_pre = [Eq n [n0,I c_objD,no]]
  -- get solutions to TVs
  o = solutionAn_get sol a
  a0 = a+1
  -- infer type
  (ap,bp,types,gp,n1,c_1) = ag_fields (a0,b0,g,[n0],sol) fields
  to = objectP_from_list NotRec types
  c_o = makeEqual_all o (to,no,no)
  c |trace 35 ("Equalised by " ++ show c_o) True = []
 in (ap,bp,o,gp,n1,concat[c,c_pre,c_1,c_o])

--ag_Twhile :: Con_in -> (JSNode,JSNode) -> Con_out
--ag_Twhile (a,b,g,n,sol) (bool,e) = let
  -- -- create variables
  -- b0 = b
  -- a0 = a
  -- -- infer types
  -- (a1,b1,_tb,n1,g1,c_1) = ag_Statement (a0,b0,g ,n ,sol) bool
  -- (a2,b2,_te,n2,g2,c_2) = ag_Statement (a1,b1,g1,n1,sol) e
  -- c_g = context_sub_constrain g2 g
  -- c = [Gt [n2] [n1]]
  -- in (a2,b2,JST0P_None,n1,g1,concat [c,c_1,c_2,c_g])

-- ag_Tfor :: Con_in -> ([JSNode],JSNode,JSNode,JSNode) -> Con_out
-- ag_Tfor (a,b,g,n,sol) (e1,e2,e3,body) = let
--   (a1,b1,t1,n1,g1,c_1) = ag_Stmt_mult (a ,b ,g ,n ,sol) e1
--   (a2,b2,t2,n2,g2,c_2) = ag_Statement (a1,b1,g1,n1,sol) e2
--   (a3,b3,t3,n3,g3,c_3) = ag_Stmt_mult (a2,b2,g2,n2,sol) [body,e3]
--   c_g = context_sub_constrain g3 g1
--   c = [Gt [n3] [n1]]
--   in (a3,b3,JST0P_None,n2,g2,concat [c_1,c_2,c,c_3])

show_fields :: [(String,[JSNode])] -> String
show_fields [] = ""
show_fields [(s,j)] = s ++ ":" ++ renderExpressionToString j
show_fields ((s,j):js) = s ++ ":" ++ renderExpressionToString j ++ "," ++ show_fields js

ag_OPPlus :: Con_in -> ([JSNode],[JSNode]) -> Con_out
ag_OPPlus (a,b,g,n,sol) (e1,e2) = let
  t = solutionAn_get sol a
  a0 = a+1
  b0 = b
  (a1,b1,t1,g1,n1,c_1) = ag_Expression (a0,b0,g ,n ,sol) e1
  (a2,b2,t2,g2,n2,c_2) = ag_Expression (a1,b1,g1,n1,sol) e2
  c = []
  in (a2,b2,t,g2,n2,concat [c_1,c_2,c])

ag_OPComparison :: Con_in -> ([JSNode],[JSNode]) -> Con_out
ag_OPComparison (a,b,g,n,sol) (js1,js2) = let
  (a1,b1,t1,g1,n1,c_1) = ag_Expression (a ,b ,g ,n ,sol) js1
  (a2,b2,t2,g2,n2,c_2) = ag_Expression (a1,b1,g1,n1,sol) js2
  in (a2,b2,(JST0P_Bool,I 0,I 0),g2,n2,concat[c_1,c_2])

ag_OPArithmetic :: Con_in -> ([JSNode],[JSNode]) -> Con_out
ag_OPArithmetic (a,b,g,n,sol) (js1,js2) = let
  (a1,b1,t1,g1,n1,c_1) = ag_Expression (a ,b ,g ,n ,sol) js1
  (a2,b2,t2,g2,n2,c_2) = ag_Expression (a1,b1,g1,n1,sol) js2
  in (a2,b2,(JST0P_Int,I 0,I 0),g1,n2,concat[c_1,c_2])

ag_OPLogic :: Con_in -> ([JSNode],[JSNode]) -> Con_out
ag_OPLogic (a,b,g,n,sol) (js1,js2) = let
  t = solutionAn_get sol a
  a0 = a+1
  (a1,b1,t1,g1,n1,c_1) = ag_Expression (a0,b ,g ,n ,sol) js1
  (a2,b2,t2,g2,n2,c_2) = ag_Expression (a1,b1,g1,n1,sol) js2
  c = makeMin t t1 t2
  in (a2,b2,t,g2,n2,concat[c_1,c_2,c])

ag_OPBang :: Con_in -> [JSNode] -> Con_out
ag_OPBang (a,b,g,n,sol) js = let
  (a1,b1,t1,g1,n1,c_1) = ag_Expression (a,b,g,n,sol) js
  in (a1,b1,(JST0P_Bool,I 0,I 0),g1,n1,c_1)

ag_OPSign :: Con_in -> [JSNode] -> Con_out
ag_OPSign (a,b,g,n,sol) js = let
  (a1,b1,t1,g1,n1,c_1) = ag_Expression (a,b,g,n,sol) js
  in (a1,b1,(JST0P_Int,I 0,I 0),g1,n1,c_1)

ag_OPIntPF :: Con_in -> [JSNode] -> Con_out
ag_OPIntPF (a,b,g,n,sol) js = let
  (a1,b1,t1,g1,n1,c_1) = ag_Expression (a,b,g,n,sol) js
  in (a1,b1,(JST0P_Int,I 0,I 0),g1,n1,c_1)

ag_OPCond :: Con_in -> ([[JSNode]],[[JSNode]],[[JSNode]]) -> Con_out
ag_OPCond (a,b,g,n,sol) (cond,true,false) | trace 10 ("(AG)TCondOP: " ++ renderExpressionListToString cond  ++ " ? " ++ renderExpressionListToString true ++ ":" ++ renderExpressionListToString false ++ "->" ++ show c_cond) False = undefined
ag_OPCond (a,b,g,n,sol) (cond,true,false) = let
 -- create new variables
  npost = N b
  n0 = N (b+1)
  b0 = b+2
  c0 = [Eq [n0,I c_cond] n]
  -- get solution for TVs
  t = solutionAn_get sol a
  a0 = a+1
  -- infer type
  (a1,b1,_tb,g1,n1p,c_1) = ag_Exp_mult (a0,b0 ,g ,[n0],sol) cond
  (a2,b2,_tt,g2,n2p,c_2) = ag_Exp_mult (a1,b1 ,g1,n1p ,sol) true
  (a3,b3,_tf,g3,n3p,c_3) = ag_Exp_mult (a2,b2 ,g1,n1p ,sol) false
  c = [Gt n2p [npost],
       Gt n3p [npost]]
  (c_G,gammar,a4,b4) = context_min_constrain g2 g3 (a3,b3)
  in (a4,b4,t,gammar,[npost],concat [c,c0,c_1,c_2,c_3,c_G])


ag_TstringLit :: Con_in -> String -> Con_out
ag_TstringLit (a,b,g,n,_sol) _s =
  (a,b,(JST0P_String "",I 0,I 0),g,n,[])

ag_Treturn :: Con_in -> [[JSNode]] -> Con_out
ag_Treturn (a,b,g,n,sol) js = let
  (ap,bp,tp,np,gp,cp) = ag_Exp_mult (a,b,g,n,sol) js
  in (ap,bp,(JST0P_Ret tp,I 0,I 0),np,gp,cp)

-- Return tag cannot handle:
-- returns as potential assignment a= if b {Return 3} else 5

----------------------------------------
-- Auxiliary Functions
----------------------------------------

list2DefAn :: [TypeAn] -> [(TypeAn,FieldType)]
list2DefAn = Prelude.map (\t->(t,Definite))

ag_fields :: Con_in -> [(String,[JSNode])] -> (Int,Int,[(String,TypeAn)],ContextAn,[Annotation],[ConstrainAn])
ag_fields (a,b,g,n,_sol) [] = (a,b,[],g,n,[])
ag_fields (a,b,g,n,sol) ((s,js):jx) = let
  -- create new TVs
  nts = N b
  np = N (b+1)
  b0 = b+2
  --inference
  (as,bs,ts,gs,ns,c_s) = ag_Expression (a,b0,g,n,sol) js
  (ax,bx,l ,gx,nx,c_x) = ag_fields (as,bs,gs,ns,sol) jx
  c | trace 10 ("(AG)TmemW: {}." ++ s ++ "=" ++ renderExpressionToString js ++ " -> " ++ show (c_memW Potential)) True = [Eq [I (c_memW Potential),np] nx]
  in (ax,bx,(s,ts):l,gx,[np],concat[c,c_s,c_x])

ag_ArgList :: Int -> [String] -> SolutionAn -> (Int,[TypeAn],[ConstrainAn])
ag_ArgList a [] _sol = (a,[],[])
ag_ArgList a (_x:xs) sol = let --name of argument has already been analysed by cg
  tx = solutionAn_get sol a
  cx = makeSuff tx
  (as,txs,cxs) = ag_ArgList (a+1) xs sol
  in (as,tx:txs, concat [cx,cxs])

ag_ArgList_copy :: Int -> [a] -> Int
ag_ArgList_copy a xs | trace 2 ("(  )Arglist_copy: " ++ show a ++ ", " ++ show (Prelude.length xs)) False = undefined
ag_ArgList_copy a xs = a + (Prelude.length xs)
              
----------------------------------------
-- First pass
----------------------------------------

type PP2_in = (Int,Int,SolutionAn,ContextAn)
type PP2_out = (Int,Int,ContextAn,Int)

in2out :: PP2_in -> Int -> PP2_out
in2out (a,b,_sol,gamma) i = (a,b,gamma,i)

out2in :: PP2_out -> SolutionAn -> PP2_in
out2in (a,b,gamma,_i) sol = (a,b,sol,gamma)

pp2_Statement :: PP2_in -> JSNode -> PP2_out
pp2_Statement _g j | trace 30 ("\npp2_JSNode : " ++ (show j)) False = undefined
pp2_Statement g (NT n _l _c) = pp2_Statement g (NN n)
pp2_Statement g (NN n)
  | is_SourceElementsTop_JS (NN n) = pp2_Stmt_mult g (ex_SourceElementsTop n)
  | is_Variables_JS         (NN n) = pp2_Stmt_mult g (ex_Variables         n)
  | is_Block_JS             (NN n) = pp2_Stmt_mult g (ex_Block             n)
  | is_Expression_JS        (NN n) = pp2_Exp_Stmt  g (ex_Expression        n)
  | is_ExpressionParen_JS   (NN n) = pp2_Exp_Stmt  g (ex_ExpressionParen   n)

  -- unneccessary
  | is_emptyLiteral_JS (NN n) = fun_in2out g 0
  | is_semicolon_JS    (NN n) = fun_in2out g 0
                                
  -- handled language features
  | is_Tcond_JS   (NN n) = pp2_Tcond   g (ex_Tcond    (NN n))
  | is_funStmt_JS (NN n) = pp2_funStmt g (ex_TfunStmt (NN n))
  | is_TvarD_JS   (NN n) = pp2_TvarD   g (ex_TvarD    (NN n))
  | is_Twhile_JS  (NN n) = pp2_Twhile  g (ex_Twhile   (NN n))
  | is_Tfor_JS    (NN n) = pp2_Tfor    g (ex_Tfor     (NN n))
  | is_Treturn_JS (NN n) = pp2_Treturn g (ex_Treturn  (NN n))
pp2_Statement (a,b,_sol,gamma) j | error ("PP2: Expression not handled" ++ show j) = (a,b,gamma,0)
                                 | True = undefined

pp2_Stmt_mult :: PP2_in -> [JSNode] -> PP2_out
pp2_Stmt_mult g [] = fun_in2out g 0
pp2_Stmt_mult g [j] = pp2_Statement g j
pp2_Stmt_mult (a,b,sol,gamma) (j:js) = let
  (a1,b1,gamma1,i1) = pp2_Statement (a ,b ,sol,gamma ) j
  (a2,b2,gamma2,i2) = pp2_Stmt_mult (a1,b1,sol,gamma1) js
  in (a2,b2,gamma2,i1+i2)

pp2_Exp_Stmt :: PP2_in -> [[JSNode]] -> PP2_out
pp2_Exp_Stmt = pp2_Exp_mult

pp2_Expression :: PP2_in -> [JSNode] -> PP2_out
pp2_Expression g js_dirty = let
  js = filter_irrelevant js_dirty
  res  
    | is_Tnull_JS js      = fun_in2out g 0
    | is_Tint_JS js       = fun_in2out g 0
    | is_TboolLit_JS js   = pp2_TboolLit   g
    | is_TstringLit_JS js = pp2_TstringLit g (ex_TstringLit js)
    | is_TobjLit_JS js    = pp2_TobjLit    g (ex_TobjLit    js)

    | is_TvarR_JS js  = fun_in2out g 0
    | is_TvarW_JS js  = pp2_TvarW  g (ex_TvarW  js)
    | is_TmemR_JS js  = pp2_TmemR  g (ex_TmemR  js)
    | is_TmemW1_JS js = pp2_TmemW1 g (ex_TmemW1 js)
    | is_TmemW2_JS js = pp2_TmemW2 g (ex_TmemW2 js)
    | is_TmemX_JS js  = pp2_TmemX  g (ex_TmemX  js)
    | is_TfunX_JS js  = pp2_TfunX  g (ex_TfunX  js)
    | is_TnewX_JS js  = pp2_TfunX  g (ex_TnewX  js)

    | is_funExpr_JS js = pp2_funExpr g (ex_TfunExpr js)

    | is_OPPlus_JS       js = pp2_OPPlus       g (ex_BinOp js)
    | is_OPArithmetic_JS js = pp2_OPArithmetic g (ex_BinOp js)
    | is_OPComparison_JS js = pp2_OPComparison g (ex_BinOp js)
    | is_OPLogic_JS      js = pp2_OPLogic      g (ex_BinOp js)
    | is_OPBang_JS       js = pp2_OPBang       g (ex_UnOp  js)
    | is_OPSign_JS       js = pp2_OPSign       g (ex_UnOp  js)
    | is_OPCond_JS       js = pp2_OPCond       g (ex_TerOp js)

    | is_Statement_single js = pp2_Stmt_mult g js
    | js == [] = fun_in2out g 0
  in res

pp2_Exp_mult :: PP2_in -> [[JSNode]] -> PP2_out
pp2_Exp_mult g [] = fun_in2out g 0
pp2_Exp_mult g [j] = pp2_Expression g j
pp2_Exp_mult (a,b,sol,g) (js:jss) = let
  (a1,b1,g1,i1) = pp2_Expression (a ,b ,sol,g ) js
  (a2,b2,g2,i2) = pp2_Exp_mult   (a1,b1,sol,g1) jss
  in (a2,b2,g2,i1+i2)

pp2_TvarW :: PP2_in -> (String,[JSNode]) -> PP2_out
pp2_TvarW g (_x,e) = pp2_Expression g e

pp2_TmemR :: PP2_in -> ([JSNode],String) -> PP2_out
pp2_TmemR g (e,_m) = pp2_Expression g e

pp2_TmemW1 :: PP2_in -> (String,String,[JSNode]) -> PP2_out
pp2_TmemW1 g (_var,_m,e) = pp2_Expression g e

pp2_TmemW2 :: PP2_in -> ([JSNode],String,[JSNode]) -> PP2_out
pp2_TmemW2 g (e1,_m,e2) = pp2_Exp_mult g [e1,e2]

pp2_TmemX :: PP2_in -> ([JSNode],String,[[JSNode]]) -> PP2_out
pp2_TmemX g (e1,_m,e2) = pp2_Exp_mult g (e1:e2)

pp2_TfunX :: PP2_in -> ([JSNode],[[JSNode]]) -> PP2_out
pp2_TfunX g (ef,ei) = pp2_Exp_mult g (ef:ei)

pp2_Tcond :: PP2_in -> ([[JSNode]],JSNode,JSNode) -> PP2_out
pp2_Tcond (a,b,sol,gamma) (e1,e2,e3) = let
  (a1,b1,g1,i1) = pp2_Exp_mult (a,b,sol,gamma) e1
  (a2,b2,g2,i2) = pp2_Stmt_mult (a1,b1,sol,g1) [e2,e3]
  in (a2,b2,g2,i1+i2)

pp2_TvarD :: PP2_in -> (String,[JSNode]) -> PP2_out
pp2_TvarD (a,b,sol,gamma) (var,e) | trace 30 ("(" ++ show b ++ ")PP2_TvarD " ++ var) False = undefined
pp2_TvarD (a,b,sol,gamma) (var,e) = let
  tvar = solutionAn_get sol a --JST0_TV a (var ++ "Decl")
  b0 = b
  a0 = a+1
  gammap = var_set gamma var (tvar,Potential)
  (ap,bp,gp,ip) = pp2_Expression (a0,b0,sol,gammap) e
  in (ap,bp,gp,ip+c_varDi)

pp2_funExpr :: PP2_in -> (String,[String],JSNode) -> PP2_out
pp2_funExpr (_a,_b,_sol,_gamma) (f,_x,_e) | trace 30 ("pp2_TfunExpr " ++ show f) False = undefined
pp2_funExpr (a,b,_sol,gamma) (_f,_x,_e) = (a,b,gamma,0)

pp2_funStmt :: PP2_in -> (String,[String],JSNode) -> PP2_out
pp2_funStmt (_a,_b,_sol,_gamma) (f,_x,_e) | trace 30 ("pp2_TfunStmt " ++ show f) False = undefined
pp2_funStmt (a,b,_sol,gamma) (_f,_x,_e) = (a,b,gamma,0)

pp2_TobjLit :: PP2_in -> [(String,[JSNode])] -> PP2_out
pp2_TobjLit g [] = in2out g 0
pp2_TobjLit (a,b,sol,g) ((_s,js):jx) = let
  (a1,b1,g1,i1) = pp1_Expression (a ,b ,sol,g ) js
  (a2,b2,g2,i2) = pp1_TobjLit    (a1,b1,sol,g1) jx 
  in (a2,b2,g2,i1+i2)

pp2_Twhile :: PP2_in -> (JSNode,JSNode) -> PP2_out
pp2_Twhile (a,b,sol,g) (bool,s) = pp2_Stmt_mult (a,b,sol,g) [bool,s]

pp2_Tfor :: PP2_in -> ([JSNode],JSNode,JSNode,JSNode) -> PP2_out
pp2_Tfor (a,b,sol,g) (e1,e2,e3,body) = pp2_Stmt_mult (a,b,sol,g) (e2:e3:body:e1)

pp2_OPPlus :: PP2_in -> ([JSNode],[JSNode]) -> PP2_out
pp2_OPPlus g (e1,e2) = pp2_Exp_mult g [e1,e2]
 
pp2_OPArithmetic:: PP2_in -> ([JSNode],[JSNode]) -> PP2_out
pp2_OPArithmetic g (e1,e2) = pp2_Exp_mult g [e1,e2]

pp2_OPComparison :: PP2_in -> ([JSNode],[JSNode]) -> PP2_out
pp2_OPComparison g (e1,e2) = pp2_Exp_mult g [e1,e2]

pp2_OPLogic :: PP2_in -> ([JSNode],[JSNode]) -> PP2_out
pp2_OPLogic g (e1,e2) = pp2_Exp_mult g [e1,e2]

pp2_OPBang :: PP2_in -> [JSNode] -> PP2_out
pp2_OPBang g e = pp2_Expression g e

pp2_OPSign :: PP2_in -> [JSNode] -> PP2_out
pp2_OPSign g e = pp2_Expression g e

pp2_OPIntPF :: PP2_in -> [JSNode] -> PP2_out
pp2_OPIntPF g e = pp2_Expression g e

pp2_OPCond :: PP2_in -> ([[JSNode]],[[JSNode]],[[JSNode]]) -> PP2_out
pp2_OPCond g (cond,true,false) = pp2_Exp_mult g (concat[cond,true,false])

pp2_TstringLit :: PP2_in -> String -> PP2_out
pp2_TstringLit (a,b,_sol,gamma) _s = (a,b,gamma,0)

pp2_TboolLit :: PP2_in -> PP2_out
pp2_TboolLit (a,b,_sol,gamma) = (a,b,gamma,0)

pp2_Treturn :: PP2_in -> [[JSNode]] -> PP2_out
pp2_Treturn = pp2_Exp_mult

----------------------------------------
-- Function pass
----------------------------------------

type PP1_in = (Int,Int,SolutionAn,ContextAn)
type PP1_out = (Int,Int,ContextAn,Int)

fun_in2out :: PP1_in -> Int -> PP1_out
fun_in2out (a,b,_sol,gamma) i = (a,b,gamma,i)

fun_out2in :: PP1_out -> SolutionAn -> PP1_in
fun_out2in (a,b,gamma,_i) sol = (a,b,sol,gamma)

pp1_Statement :: PP1_in -> JSNode -> PP1_out
pp1_Statement _g j | trace 30 ("\npp1_Statement : " ++ (show j)) False = undefined
pp1_Statement g (NT n _l _c) = pp1_Statement g (NN n)
pp1_Statement g (NN n)
  -- boxes
  | is_SourceElementsTop_JS (NN n) = pp1_Stmt_mult g (ex_SourceElementsTop n)
  | is_Variables_JS         (NN n) = pp1_Stmt_mult g (ex_Variables         n)
  | is_Block_JS             (NN n) = pp1_Stmt_mult g (ex_Block             n)
  | is_Expression_JS        (NN n) = pp1_Exp_Stmt  g (ex_Expression        n)
  | is_ExpressionParen_JS   (NN n) = pp1_Exp_Stmt  g (ex_ExpressionParen   n)

  -- unneccessary
  | is_emptyLiteral_JS (NN n) = fun_in2out g 0
  | is_semicolon_JS    (NN n) = fun_in2out g 0
                                
  -- handled language features
  | is_Tcond_JS   (NN n) = pp1_Tcond     g (ex_Tcond    (NN n))
  | is_funStmt_JS (NN n) = pp1_funStmt   g (ex_TfunStmt (NN n))
  | is_TvarD_JS   (NN n) = pp1_TvarD     g (ex_TvarD    (NN n))
  | is_Twhile_JS  (NN n) = pp1_Twhile    g (ex_Twhile   (NN n))
  | is_Tfor_JS    (NN n) = pp1_Tfor      g (ex_Tfor     (NN n))
  | is_Treturn_JS (NN n) = pp1_Treturn   g (ex_Treturn  (NN n))
pp1_Statement (a,b,_sol,gamma) j | error ("PP1: Expression not handled" ++ show j) = (a,b,gamma,0)
                                 | True = undefined

pp1_Stmt_mult :: PP1_in -> [JSNode] -> PP1_out
pp1_Stmt_mult g [] = fun_in2out g 0
pp1_Stmt_mult g [j] = pp1_Statement g j
pp1_Stmt_mult (a,b,sol,gamma) (j:js) = let
  (a1,b1,gamma1,i1) = pp1_Statement (a ,b ,sol,gamma ) j
  (a2,b2,gamma2,i2) = pp1_Stmt_mult (a1,b1,sol,gamma1) js
  in (a2,b2,gamma2,i1+i2)

pp1_Exp_Stmt :: PP1_in -> [[JSNode]] -> PP1_out
pp1_Exp_Stmt = pp1_Exp_mult

pp1_Expression :: PP1_in -> [JSNode] -> PP1_out
pp1_Expression g js_dirty = let
  js = filter_irrelevant js_dirty
  res  
    | is_Tnull_JS js      = fun_in2out g 0
    | is_Tint_JS js       = fun_in2out g 0
    | is_TboolLit_JS js   = pp1_TboolLit   g
    | is_TstringLit_JS js = pp1_TstringLit g (ex_TstringLit js)
    | is_TobjLit_JS js    = pp1_TobjLit    g (ex_TobjLit    js)

    | is_TvarR_JS  js = fun_in2out g 0
    | is_TvarW_JS  js = pp1_TvarW  g (ex_TvarW  js)
    | is_TmemR_JS  js = pp1_TmemR  g (ex_TmemR  js)
    | is_TmemW1_JS js = pp1_TmemW1 g (ex_TmemW1 js)
    | is_TmemW2_JS js = pp1_TmemW2 g (ex_TmemW2 js)
    | is_TmemX_JS  js = pp1_TmemX  g (ex_TmemX  js)
    | is_TfunX_JS  js = pp1_TfunX  g (ex_TfunX  js)
    | is_TnewX_JS  js = pp1_TfunX  g (ex_TnewX  js)

    | is_funExpr_JS js = pp1_funExpr g (ex_TfunExpr js)


    | is_OPPlus_JS       js = pp1_OPPlus       g (ex_BinOp js)
    | is_OPArithmetic_JS js = pp1_OPArithmetic g (ex_BinOp js)
    | is_OPComparison_JS js = pp1_OPComparison g (ex_BinOp js)
    | is_OPLogic_JS      js = pp1_OPLogic      g (ex_BinOp js)
    | is_OPBang_JS       js = pp1_OPBang       g (ex_UnOp  js)
    | is_OPSign_JS       js = pp1_OPSign       g (ex_UnOp  js)
    | is_OPCond_JS       js = pp1_OPCond       g (ex_TerOp js)
    | is_OPIntPostfix_JS js = pp1_OPIntPF      g (ex_PostfixOp  js)

    | is_Statement_single js = pp1_Stmt_mult g js
    | js == [] = fun_in2out g 0
  in res

pp1_Exp_mult :: PP1_in -> [[JSNode]] -> PP1_out
pp1_Exp_mult g [] = fun_in2out g 0
pp1_Exp_mult g [j] = pp1_Expression g j
pp1_Exp_mult (a,b,sol,gamma) (j:js) = let
  (a1,b1,gamma1,i1) = pp1_Expression (a ,b ,sol,gamma ) j
  (a2,b2,gamma2,i2) = pp1_Exp_mult   (a1,b1,sol,gamma1) js
  in (a2,b2,gamma2,i1+i2)

pp1_TvarW :: PP1_in -> (String,[JSNode]) -> PP1_out
pp1_TvarW g (_x,e) = pp1_Expression g e

pp1_TmemR :: PP1_in -> ([JSNode],String) -> PP1_out
pp1_TmemR g (e,_m) = pp1_Expression g e

pp1_TmemW1 :: PP1_in -> (String,String,[JSNode]) -> PP1_out
pp1_TmemW1 g (_var,_m,e) = pp1_Expression g e

pp1_TmemW2 :: PP1_in -> ([JSNode],String,[JSNode]) -> PP1_out
pp1_TmemW2 g (e1,_m,e2) = pp1_Exp_mult g [e1,e2]

pp1_TmemX :: PP1_in -> ([JSNode],String,[[JSNode]]) -> PP1_out
pp1_TmemX g (e1,_m,e2) = pp1_Exp_mult g (e1:e2)

pp1_TfunX :: PP1_in -> ([JSNode],[[JSNode]]) -> PP1_out
pp1_TfunX g (ef,ei) = pp1_Exp_mult g (ef:ei)

pp1_Tcond :: PP1_in -> ([[JSNode]],JSNode,JSNode) -> PP1_out
pp1_Tcond (a,b,sol,gamma) (e1,e2,e3) = let
  (a1,b1,g1,i1) = pp1_Exp_mult (a,b,sol,gamma) e1
  (a2,b2,g2,i2) = pp1_Stmt_mult (a1,b1,sol,g1) [e2,e3]
  in (a2,b2,g2,i1+i2)

pp1_TvarD :: PP1_in -> (String,[JSNode]) -> PP1_out
pp1_TvarD (a,b,sol,gamma) (_var,e) = pp1_Expression (a,b,sol,gamma) e

pp1_funExpr :: PP1_in -> (String,[String],JSNode) -> PP1_out
pp1_funExpr (a,b,_sol,gamma) (_f,_x,_e) = (a,b,gamma,0)

pp1_funStmt :: PP1_in -> (String,[String],JSNode) -> PP1_out
pp1_funStmt (a,b,sol,gamma) (f,_x,_e) = let
  tf = solutionAn_get sol a
  gammap = var_set gamma f (tf,Definite)
  in (a+1,b,gammap,c_funDi)

pp1_TobjLit :: PP1_in -> [(String,[JSNode])] -> PP1_out
pp1_TobjLit g [] = fun_in2out g 0
pp1_TobjLit (a,b,sol,g) ((_s,js):jx) = let
  (a1,b1,g1,i1) = pp1_Expression (a ,b ,sol,g ) js
  (a2,b2,g2,i2) = pp1_TobjLit    (a1,b1,sol,g1) jx 
  in (a2,b2,g2,i1+i2)

pp1_Twhile :: PP1_in -> (JSNode,JSNode) -> PP1_out
pp1_Twhile (a,b,sol,g) (bool,s) = pp1_Stmt_mult (a,b,sol,g) [bool,s]

pp1_Tfor :: PP1_in -> ([JSNode],JSNode,JSNode,JSNode) -> PP1_out
pp1_Tfor (a,b,sol,g) (e1,e2,e3,body) = pp1_Stmt_mult (a,b,sol,g) (e2:e3:body:e1)

pp1_OPPlus :: PP1_in -> ([JSNode],[JSNode]) -> PP1_out
pp1_OPPlus g (e1,e2) = pp1_Exp_mult g [e1,e2]
 
pp1_OPArithmetic:: PP1_in -> ([JSNode],[JSNode]) -> PP1_out
pp1_OPArithmetic g (e1,e2) = pp1_Exp_mult g [e1,e2]

pp1_OPComparison :: PP1_in -> ([JSNode],[JSNode]) -> PP1_out
pp1_OPComparison g (e1,e2) = pp1_Exp_mult g [e1,e2]

pp1_OPLogic :: PP1_in -> ([JSNode],[JSNode]) -> PP1_out
pp1_OPLogic g (e1,e2) = pp1_Exp_mult g [e1,e2]

pp1_OPBang :: PP1_in -> [JSNode] -> PP1_out
pp1_OPBang g e = pp1_Expression g e

pp1_OPCond :: PP1_in -> ([[JSNode]],[[JSNode]],[[JSNode]]) -> PP1_out
pp1_OPCond g (cond,true,false) = pp1_Exp_mult g (concat[cond,true,false])

pp1_OPSign :: PP1_in -> [JSNode] -> PP1_out
pp1_OPSign g e = pp1_Expression g e

pp1_OPIntPF :: PP1_in -> [JSNode] -> PP1_out
pp1_OPIntPF g e = pp1_Expression g e

pp1_TstringLit :: PP1_in -> String -> PP1_out
pp1_TstringLit (a,b,_sol,gamma) _s = (a,b,gamma,0)

pp1_TboolLit :: PP1_in -> PP1_out
pp1_TboolLit (a,b,_sol,gamma) = (a,b,gamma,0)

pp1_Treturn :: PP1_in -> [[JSNode]] -> PP1_out
pp1_Treturn (a,b,sol,gamma) js = pp1_Exp_mult (a,b,sol,gamma) js
