module Main where

import Language.JavaScript.Parser.Parser
import Language.JavaScript.Parser.AST
import Language.JavaScript.Pretty.Printer

import JST0_constrain
import JST0_type_aux
import JST0_solution
import JST0_types
import qualified JST0_context

import JST0P_context
import JST0P_solution
import JST0P_types
import JST0P_constrain

import API_model
import ConstGen
import Closure
import AnnotGen
import Res_model

import Control.Monad.LPMonad
import Data.LinearProgram

import Data.Map as Map
import Maps

import Debugging

import Control.DeepSeq

type Output_function_old = (ReturnCode -> (Int,Map Int String,Int,Int,[Constrain],Map Int CSet,[ConstrainAn],ContextAn,ContextAn,Maybe (Double, Map String Double),TypeAn,Annotation,SolutionAn) -> IO())

type Output_function = ReturnCode -> (Int, Map Int String, [Constrain]  , Map Int CSet, JST0_context.Context            , JST0_context.Context,              Type  , Solution)
                                  -> (Int,                 [ConstrainAn],               ContextAn           , Annotation, ContextAn           , Annotation , TypeAn, SolutionAn, Maybe (Double, Map String Double)) -> IO()

main :: IO()
main = do
  fname <- getLine
  ti_file fname

--fp_string :: String -> IO()
--fp_string s = let
--  p = parse s "test.js"
--  in fp_EAST p

ti_string :: String -> IO()
ti_string s = let
  p = parse s "test.js"
  in ti_EAST print_summary p

tis_string :: String -> IO()
tis_string s = let
  p = parse s "test.js"
  in ti_EAST print_simple_summary p

ti_test :: IO()
ti_test = do
  output "--------------------------------------------\n"
  let s ="43" in ti_EAST (test_run s c_val) (parse s "test.js")
  let s ="var x" in ti_EAST (test_run s c_varD) (parse s "test.js")
  let s ="var x=4" in ti_EAST (test_run s (c_varD + c_varW + c_val)) (parse s "test.js")
  let s ="var x=4;x" in ti_EAST (test_run s (c_varD + c_varW + c_varR + c_val + c_seq)) (parse s "test.js")
  let s ="var x;x=4" in ti_EAST (test_run s (c_varD + c_varW + c_val + c_seq)) (parse s "test.js")
  let s ="return {m:2}" in ti_EAST (test_run s (c_objD + c_memW Potential + c_val)) (parse s "test.js")
  let s ="var x={m:2}"  in ti_EAST (test_run s (c_objD + c_memW Potential + c_val + c_varD + c_varW)) (parse s "test.js")
  let s ="var x={m:2};return x.m"  in ti_EAST (test_run s (c_objD + c_memW Potential + c_val + c_varD + c_varW+c_seq + c_varR + c_memR)) (parse s "test.js")
  let s ="var x={m:2};x.m=3" in ti_EAST (test_run s (c_objD + c_varD + c_varW + c_memW Potential + c_val + c_seq + c_varR + c_memW Potential + c_val)) (parse s "test.js")
  let s ="var x={m:2};x.m;x.m=3" in ti_EAST (test_run s ( c_objD + c_varD + c_varW + c_memW Potential + c_val + c_seq + c_memR + c_seq + c_varW + c_memW Definite + c_val)) (parse s "test.js")
  let s = "return true?3:4" in ti_EAST (test_run s (c_cond+c_val+c_val)) (parse s "test.js")
  let s ="function f(x) {x.next}"  in ti_EAST (test_run s (c_funD)) (parse s "test.js")
  let s = "function f(x) {f(x.next)};var x={next:null}; var y={next:x};f(y)" in ti_EAST (test_run s (c_funD + c_seq + c_varD + c_objD + c_memW Potential + c_varW + c_seq + c_varD + c_objD + c_memW Potential + c_varR + c_seq + c_varR + c_varR + c_funX + c_varR + c_varR + c_memR + c_funX)) (parse s "test.js")
  output "--------------------------------------------\n\n\n"
  

-- type inference for an Either AST or ErrorString
ti_EAST :: (Output_function) -> Either String JSNode -> IO()
ti_EAST out p = case p of
    (Left e) -> putStr ("Parsing Error: " ++ e)
    Right j -> let
-- initialise Context with API types
      g_init | trace 5 ("computing API model") True = init_context
             | True = undefined
      gminus_init | trace 5 ("reducing API model") True = deg_context g_init
                  |True = undefined
-- Generate Constraints
      (typesCount,t,gminus_post,constraints) = constGen (0,gminus_init) j
-- Close type constraints
      constraintsClosed = close_constraints constraints 0 (Prelude.length constraints) 
-- Extract solution
      hl = extract_HL_types constraintsClosed
      typeVars = JST0_constrain.get_TVs_list constraints
      sol = extract_solution constraintsClosed
      sum = show sol
      well_defined = sum `deepseq` JST0_solution.check_solution sol constraints
-- Augment Context/Solution
      (solP,b_sol) | well_defined = solutionAn_from_solution sol
                   | error "Solution to type constraints not well defined" = undefined
      g_initSol = sol_set g_init solP
-- Generate annotation Constraints
      (b_f,t_f,n_f,g_func,g_f,c_f) = annotConstGen (b_sol,g_initSol,solP) j
      n_post = N b_f
      b_f0 = b_f +1
      c_fpost = (Eq [n_post] n_f):c_f
      --(lp_suc,lp_sol) = (Success,Just (0.0,Map.empty))
      in do
        (lp_suc,lp_sol) <- glpSolveVars mipDefaults (lp (b_f0) (g_init,b_sol) c_fpost)

--        output ("Constraints: " ++ show c_fpost ++ "\n")
        out lp_suc (typesCount,typeVars,constraints,constraintsClosed,gminus_init,gminus_post,t,sol) (b_f0,c_fpost,g_init,N b_sol,g_f,n_post,t_f,solP,lp_sol)

--        (typesCount,typeVars,b_f0,b_sol,constraints,constraintsClosed,c_fpost,g_init,g_f,lp_sol,t_f,n_post,solP)

ti_file :: String -> IO()
ti_file fname = do
                s <- readFile fname
                ti_string s


compute :: String -> IO()
compute "" = putStr "."
compute _ = putStr ""

test_run :: String -> Int -> (Output_function)
test_run exercise exp_solution Success _ (_,_,_,n_pre,_,_,_,_,lpSolution)
  | (get_potential_Ann n_pre (get_sol lpSolution)) == (fromIntegral exp_solution) = do
      output ("Test " ++ exercise ++ ":" ++ (show (get_potential_Ann n_pre (get_sol lpSolution))) ++ "/" ++ show exp_solution ++ "\n PASS\n")
  | (get_potential_Ann n_pre (get_sol lpSolution)) > (fromIntegral exp_solution) = do
      output ("Test " ++ exercise ++ ":" ++ (show (get_potential_Ann n_pre (get_sol lpSolution))) ++ "/" ++ show exp_solution ++ "\n pass\n")
  | otherwise = do
      output ("Test " ++ exercise ++ ":" ++ (show (get_potential_Ann n_pre (get_sol lpSolution))) ++ "/" ++ show exp_solution ++ "\n FAIL!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n")
  
  


print_simple_summary :: Output_function
  --ReturnCode -> (Int,Map Int String,[Constrain],Map Int CSet,JST0_context.Context,JST0_context.Context,Type,Solution) -> IO()
print_simple_summary _ (tvCount,typeVars,constraints,constraintsClosed,g_pre,g_post,type_stmt,solution) _ = do
  compute (show g_pre)
  compute (show g_post)
  compute (show tvCount)
  compute (show type_stmt)
  compute (show (length constraintsClosed))
  output "--------------------Results----------------------\n"
  output "-----Base Types----------------------------------\n"
  output ("Used variables: " ++ show tvCount ++ "\n")
  output ("Generated constraints: " ++ show (length constraints) ++ "\n")
  output (show constraints ++ "\n" )
  output ("Closed_constraints: " ++ show (Map.fold (\cm prv -> prv + (Maps.cset_count cm)) 0 constraintsClosed) ++ "\n")
  output (show constraintsClosed ++ "\n")
  output ("Variable types [before]: \n" ++ JST0_context.context_toNiceString g_pre  solution)
  output ("Variable types [after] : \n" ++ JST0_context.context_toNiceString g_post solution)
  output ("Solution: \n" ++ show_varTypes typeVars solution ++ "\n")
  output ("Result : " ++ show type_stmt ++ " :: " ++ show (type_eliminate_TVs solution type_stmt) ++ "\n")


print_summary :: Output_function
--ReturnCode -> (Int,Map Int String,Int,Int,[Constrain],Map Int CSet,[ConstrainAn],ContextAn,ContextAn,Maybe (Double, Map String Double),TypeAn,Annotation,SolutionAn) -> IO()
print_summary Success (tvCount ,typeVars,constraints,constraintsClosed,gamma_pre,      gamma_post,       type_stmt,solution)
                      (annCount         ,lpGenerated,                  g_pre    ,n_pre,g_post    ,n_post,t_stmt   ,annSolution,lpSolution) = do
--(,,,n_req,constraints,constraintsClosed,lpGenerated,g_pre,g_post,lpSolution,t_stmt,n_stmt,annSolution) = do
  --compute (show (length (Map.keys constraintsClosed)))
  compute (show tvCount)
  compute (show (length constraints))
  compute (show annCount)
  output "--------------------Results----------------------\n"
  output "-----Base Types----------------------------------\n"
  output ("Used type variables : " ++ show tvCount ++ "\n")
  output ("Generated type constraints : " ++ show (length constraints) ++ "\n")
  output ("Closed type constraints : " ++ show (Map.fold (\cm prv -> prv + (Maps.cset_count cm)) 0 constraintsClosed) ++ "\n")
  --show (length (Map.keys constraintsClosed)) ++ "\n")
  output "-----Annotations---------------------------------\n"
  output ("Used annotation variables : " ++ show annCount ++ "\n")
  output ("Generated annotation constraints : " ++ show (length lpGenerated) ++ "\n")
--  output (show lpGenerated++"\n")
  output "-----Amortised Types-----------------------------\n"
  output ("Variable types [before execution]: \n" ++ (get_full_variable_types (var_names g_pre ) g_pre  (get_sol lpSolution)) ++ "\n")
  output ("Variable types [after execution]:  \n" ++ (get_full_variable_types (var_names g_post) g_post (get_sol lpSolution)) ++ "\n")
  output ("Solution: \n" ++ Map.foldWithKey (\i s prv -> prv ++ "    " ++ (show i) ++ ": T(" ++ s ++ ")\n       " ++ printSol_An (solutionAn_get annSolution i) (get_sol lpSolution)  ++ "\n") "" typeVars)
  --output("Annotation Solution: \n" ++ lpSol_toString (get_sol lpSolution))
  output ("whole program: " ++ (show (get_potential_Ann n_pre (get_sol lpSolution))) ++ "->" ++ (printSol_An t_stmt (get_sol lpSolution)) ++ "," ++ (show (get_potential_Ann n_post (get_sol lpSolution))) ++"\n\n")
  output ("total resource need: " ++ (show (get_potential_Ann n_pre (get_sol lpSolution))) ++ get_potential_variables g_pre (get_sol lpSolution) ++ "\n")
          --show (get_res lpSolution) ++ "\n")
print_summary cod _ _ = output ("Error while solving LP:\n" ++ (show cod) ++ "\n")

lpSol_toString :: Map String Double -> String
lpSol_toString sol = Map.foldWithKey (\id v prv -> prv ++ "    " ++ id ++ ": " ++ show v ++ "\n") "" sol



print_verbal :: ReturnCode -> (Int,Int,Int,[Constrain],Map Int CSet,[ConstrainAn],ContextAn,ContextAn,Maybe (Double, Map String Double),TypeAn,Annotation,SolutionAn) -> IO()
print_verbal Success (a,b_all,b_sol,c,c_c,lp_c,gpre,gpost,lp_sol,tf,nf,solP) = do
              output "--------------------Analysing--------------------\n"
              output "-----Base Types----------------------------------\n"
              output ("Used Variables : " ++ show a ++ "\n")
              output ("Generated Constraints : " ++ show (length c) ++ "\n")
              output (show c ++ "\n" )
              output ("Closed Constraints : " ++ show (length (Map.keys c_c)) ++ "\n")
              output (show c_c ++ "\n")
              output "-----Annotations---------------------------------\n"
              output ("Used Variables : " ++ show b_all ++ "\n")
              output ("Generated Constraints : " ++ show (length lp_c) ++ "\n")
              output "-----Result--------------------------------------\n"
              output ("Variable Types [before execution]: \n" ++ (get_full_variable_types (var_names gpre ) gpre  (get_sol lp_sol)) ++ "\n")
              output ("Variable Types [after execution]:  \n" ++ (get_full_variable_types (var_names gpost) gpost (get_sol lp_sol)) ++ "\n")
              output ("Result Type: " ++ show tf ++ "\n")
              output ("whole program: " ++ (show (Map.lookup ("n_" ++ show b_sol) (get_sol lp_sol))) ++ "->" ++ (printSol_An tf (get_sol lp_sol)) ++ "," ++ (show (Map.lookup (show nf) (get_sol lp_sol))) ++"\n\n")
              output ("total resource need: " ++ show (get_res lp_sol) ++ "\n")
print_verbal cod _ = output ("Error while solving LP:\n" ++ (show cod) ++ "\n")


-- print_verbal Success _cod (dir_const,closed_const,g_minus,g_rm,g_rmSol,sol_ann,nf,tf,bstart,gf,gammap0,solP,cf,bf,nvar,nvar0,well_defined,sol,t,hl,csinfo,a,c_c,g_init,bstartp) = do
--         output ("----------------------------------------\n-- Types\n----------------------------------------\n")
--         output ("Direct Constraints: " ++ (show dir_const) ++ "\n")
--         output ("Closed Constraints: " ++ (show closed_const) ++ "\n")
--         output ("Initial Context (Reduced): " ++ (show g_minus) ++ "\n")
--         output ("Initial Context: " ++ (show g_init) ++ "\n")

--         output (show (cmap_geti c_c 38) ++ "\n")
--         output ("Used Variables: " ++ (show a) ++ "\n")
--         output ("TV Info: " ++ csinfo ++ "\n")

--         output ("Higher Level Types: " ++ (show hl) ++ "\n")
--         output ("Solution: " ++ (show_solution sol) ++ "\n")
--         output ("Type: " ++ show t ++ "\n")
--         output ("----------------------------------------\n-- Annotations\n----------------------------------------\n")
--         output ("Well-defined check: " ++ show well_defined ++ "\n")
--         output ("Annotation variables used in the solution: " ++ show bstartp ++ "\n")
--         output ("Resources used in function pass: " ++ show nvar0 ++ "\n")
--         output ("Resources used in first pass: " ++ show nvar ++ "\n")
--         output ("Variables used in actual pass: " ++ show bf ++ "\n")
--         output ("Annotations Variabels before Inference: " ++ show bstart ++ "\n")
--         output ("Annotation constraints: " ++ show cf ++ "\n")

--         output ("Initial Context: " ++ (show gammap0) ++ "\n")
--         output ("Constraints: " ++ (show cf) ++ "\n")
--         output ("Used Variables: " ++ (show bf) ++ "\n")
--         output ("Solution: " ++  show_solutionP solP ++ "\n")
--         output ("Annotation Solution: " ++ (show (get_sol sol_ann)) ++ "\n")
--         output ("----------------------------------------\n-- Results\n----------------------------------------\n")
--         output ("Variable Types [before execution]: \n" ++ (get_full_variable_types (var_names gammap0) gammap0 (get_sol sol_ann)) ++ "\n\n")
--             output ("Variable Types [after execution]: \n" ++ (get_full_variable_types (var_names gf) gf (get_sol sol_ann)) ++ "\n\n")
--             output ("whole program: " ++ show (N bstart) ++ " -> " ++ (show tf) ++ ", " ++ show nf ++ "\n")
--             output ("whole program: " ++ (show (Map.lookup ("n_" ++ show bstart) (get_sol sol_ann))) ++ "->" ++ (printSol_P tf (get_sol sol_ann)) ++ "," ++ (show (Map.lookup (show nf) (get_sol sol_ann))) ++"\n\n")
--             output ("total resource need: " ++ show (get_res sol_ann)++ "\n")
-- print_verbal _ cod _ =  output (show cod)

merge :: [a] -> [a] -> [a]
merge [] ys = ys
merge (x:xs) ys = x:(merge ys xs)

output :: String -> IO()
output s = putStr s
--output _ = return()

get_sol :: Maybe (Double, Map v Double) -> Map v Double
get_sol (Just (_,annsol)) = annsol
get_sol _ | error ("Error while finding the solution for LPP") = undefined
          | otherwise = undefined

get_res :: Maybe (Double,Map v Double) -> Double
get_res (Just (d,_)) = d
get_res _ | error ("Error while finding the soltuion for LPP") = undefined
          | otherwise = undefined

----------------------------------------
-- Construct LPPs
----------------------------------------

lp :: Int -> (ContextAn,Int) -> [ConstrainAn] -> LP String Int
lp a (g,b) cs |trace 30 ("Objective function includes: " ++ show g ++ " and " ++ show b) False = undefined
lp a (g,b) cs = execLPM $ do
  setDirection Min
  setObjective (objFun (b:(get_vars g)))
  get_lp cs
  set_pos a

get_lp :: [ConstrainAn] -> LPM String Int ()
get_lp [] = geqTo Map.empty 0
get_lp [x] = get_lp_one x
get_lp (x:xs) = do (get_lp_one x)
                   get_lp xs


-- Generates a lpp from one constraint.
get_lp_one :: ConstrainAn -> LPM String Int ()
get_lp_one (Gt a b) = let (lpos,ipos) = get_linCom   1  a
                          (lneg,ineg) = get_linCom (-1) b
                      in geqTo (linCombination (concat [lpos,lneg])) (-ineg-ipos)
get_lp_one (Eq a b) = let (lpos,ipos) = get_linCom   1  a
                          (lneg,ineg) = get_linCom (-1) b
                      in equalTo (linCombination (concat [lpos,lneg])) (-ineg-ipos)

-- convert a list of Annotations into a linear combination with the factor a for each of the summands.
-- Arguments:
--  - Factor for each of the summands
--  - List of annotations to sum up in the lin comb
-- Returns:
--  - Linear Combination of all variables
--  - Sum of all integers in the original list
get_linCom :: Int -> [Annotation] -> ([(Int,String)],Int)
get_linCom _ [] = ([],0)
get_linCom a ((N n):xs) = let
  (l,i) = get_linCom a xs
  in ((a,show (N n)):l,i)
get_linCom a ((I n):xs) = let
  (l,i) = get_linCom a xs
  in (l,i+(a*n))

set_pos :: Int -> LPM String Int ()
set_pos 0 = do varGeq "n_0" 0
set_pos a = do varGeq ("n_" ++ (show a)) 0
               set_pos (a-1)

set_varKind :: Int -> LPM String Int ()
set_varKind 0 = do setVarKind "n_0" IntVar
set_varKind a = do
  set_varKind (a-1)
  setVarKind ("n_" ++ (show a)) IntVar

objFun :: [Int] -> LinFunc String Int
objFun a | trace 30 ("Objective function " ++ show (objFun_list a)) True = linCombination (objFun_list a)

objFun_list :: [Int] -> [(Int,String)]
objFun_list is = Prelude.map (\i -> (1,"n_" ++ show i)) is

obj_3 :: LinFunc String Int
obj_3 = linCombination [(1,"n_0"),(1,"n_1"),(1,"n_2")]

-- convert the variable types into a string for all variables stored in the given context. Inside the types annotation variables are exchanged for their solution
get_full_variable_types :: [String] -> ContextAn -> Map String Double -> String
get_full_variable_types ss e m = Prelude.foldl (\prv b -> (prv ++ "       " ++ get_full_variable_type b e m ++ "\n")) "" ss

get_full_variable_type :: String -> ContextAn -> Map String Double -> String
get_full_variable_type s e m = let (t,psi) = var_get e s
                               in printSol_member s (t,psi) m

get_potential_variables :: ContextAn -> Map String Double -> String
get_potential_variables g lp_sol = Prelude.foldr (\var prv -> prv ++ " + " ++ show_potential_var var g lp_sol) "" (var_names g)

show_potential_var :: String -> ContextAn -> Map String Double -> String
show_potential_var  var g lp_sol = let (t,psi) = var_get g var
                                   in show_potential_type var t lp_sol

show_potential_type :: String -> TypeAn -> Map String Double -> String
show_potential_type var t lp_sol | isRecursive_An t = show (get_potential_An t lp_sol) ++ " x length(" ++ var ++ ")"
                                 | otherwise        = show (get_potential_An t lp_sol)

--get_potential_variable :: String -> ContextAn -> Map String Double -> Double
--get_potential_variable var g lp_sol = let (t,psi) = var_get g var
--                                      in get_potential_An t lp_sol

get_potential_members :: Map String (TypeAn,FieldType) -> Map String Double -> Double
get_potential_members mem lp_sol = Map.foldr (\(t,psi) prv -> prv + get_potential_An t lp_sol) 0 mem
                                       
get_potential_P :: TypeP -> Map String Double -> Double
get_potential_P (JST0P_Object a mem) lp_sol = get_potential_members mem lp_sol
get_potential_P _ _ = 0

get_potential_An :: TypeAn -> Map String Double -> Double
get_potential_An (t,nu,n) lp_sol = (get_potential_P t lp_sol) + get_potential_Ann nu lp_sol

get_potential_Ann :: Annotation -> Map String Double -> Double
get_potential_Ann (I n) _lp_sol = fromIntegral n
get_potential_Ann (N n) lp_sol  = let i = Map.lookup ("n_" ++ show n) lp_sol
                                  in case i of
                                      Just k -> k
                                      Nothing -> 0

printSol_P :: TypeP -> Map String Double -> String
printSol_P (JST0P_Object a mem) sol = "µ" ++ (show a) ++ ".(" ++ (printSol_members mem sol) ++ ")"
printSol_P (JST0P_Function t1 t2 n1 t3 n2) sol = "<" ++ (printSol_An t1 sol) ++ "⨯" ++ (printSol_list t2 sol) ++ "," ++ (printSol_Ann n1 sol) ++ "->" ++ (printSol_An t3 sol) ++ "," ++ (printSol_Ann n2 sol) ++ ">"
printSol_P t _sol = show t

printSol_list :: [TypeAn] -> Map String Double -> String
printSol_list xs m = "(" ++ (printSol_An_list xs m) ++ ")"

printSol_An_list :: [TypeAn] -> Map String Double -> String
printSol_An_list [] _m = ""
printSol_An_list [x] m = printSol_An x m
printSol_An_list (x:xs) m = (printSol_An x m) ++ "," ++ (printSol_An_list xs m)

printSol_P_list :: [TypeP] -> Map String Double -> String
printSol_P_list [] _m = ""
printSol_P_list [x] m = printSol_P x m
printSol_P_list (x:xs) m = (printSol_P x m) ++ "," ++ (printSol_P_list xs m)

printSol_Ann :: Annotation -> Map String Double -> String
printSol_Ann (N a) sol = let i = Map.lookup ("n_" ++ (show a)) sol
                         in case i of
                           Just k -> show k
                           Nothing -> "***Exception: Variable " ++ show i ++ "not found"
printSol_Ann a _sol = show a

printSol_members :: MembersAn -> Map String Double -> String
printSol_members mem sol = "{" ++ (Map.foldWithKey (\s ty prv -> prv ++ (printSol_member s ty sol)) "" mem) ++ "}"

printSol_member :: String -> (TypeAn,FieldType) -> Map String Double -> String
printSol_member s (t,tf) sol = (show s) ++ ":" ++ (printSol_An t sol) ++ (show tf) ++ ","

printSol_An :: TypeAn -> Map String Double -> String
printSol_An (t,nu,n) sol = "(" ++ printSol_P t sol ++ "," ++ (printSol_Ann nu sol) ++ "/" ++ printSol_Ann n sol ++ ")"
