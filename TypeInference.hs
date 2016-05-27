module Main where

import Language.JavaScript.Parser.Parser
import Language.JavaScript.Parser.AST

import JST0_constrain
import JST0_type_aux
import JST0_solution
import JST0_types
import JST0P_context
import JST0P_solution
import JST0P_types
import JST0P_constrain

import API_model
import ConstGen
import Closure
import AnnotGen

import Control.Monad.LPMonad
import Data.LinearProgram

import Data.Map as Map
import Maps

import Debugging

import Control.DeepSeq

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
  in ti_EAST p

tis_string :: String -> IO()
tis_string s = let
  p = parse s "test.js"
  in tis_EAST p

-- only infer the simple type not the annotations
tis_EAST :: Either String JSNode -> IO()
tis_EAST p = case p of
    (Left e) -> putStr ("Parsing Error: " ++ e)
    Right j -> let
-- initialise Context with API types
      g_init | trace 5 ("computing API model") True = init_context
             | True = undefined
      gminus_init | trace 5 ("reducing API model") True = deg_context g_init
                  |True = undefined
-- Generate Constraints
      (count_TV,t,_gamma,c) = constGen (0,gminus_init) j
-- Close type constraints
      c_c = close_constraints c 0 (Prelude.length c) 
-- Extract solution
      hl = extract_HL_types c_c
      csinfo = cs_show_varinfo c
      sol = extract_solution c_c
      well_defined = JST0_solution.check_solution sol c
      in
-- Solve Annotation constraints
        print_simple_summary (count_TV,csinfo,c,c_c,g_init,t,sol)

-- type inference for an Either AST or ErrorString
ti_EAST :: Either String JSNode -> IO()
ti_EAST p = case p of
    (Left e) -> putStr ("Parsing Error: " ++ e)
    Right j -> let
-- initialise Context with API types
      g_init | trace 5 ("computing API model") True = init_context
             | True = undefined
      gminus_init | trace 5 ("reducing API model") True = deg_context g_init
                  |True = undefined
-- Generate Constraints
      (count_TV,t,_gamma,c) = constGen (0,gminus_init) j
-- Close type constraints
      c_c = close_constraints c 0 (Prelude.length c) 
-- Extract solution
      hl = extract_HL_types c_c
      csinfo = cs_show_varinfo c
      sol = extract_solution c_c
      sum = show sol
      well_defined = sum `deepseq` JST0_solution.check_solution sol c
-- Augment Context/Solution
      (solP,b_sol) | well_defined = solutionAn_from_solution sol
                   | error "Solution to type constraints not well defined" = undefined
      g_initSol = sol_set g_init solP
-- Generate annotation Constraints
      (bf,tf,nf,g_func,gf,cf) = annotConstGen (b_sol,g_initSol,solP) j
      npost = N bf
      bf0 = bf +1
      cfpost = (Eq [npost] nf):cf
      in do
        output ("Used Variables : " ++ show gf ++ "\n")   
        output ("Constraints : " ++ show cf ++ "\n")   
        output csinfo
-- Solve Annotation constraints
        (lp_suc,lp_sol) <- glpSolveVars mipDefaults (lp (bf0) (g_func,b_sol) cfpost)
        print_verbal lp_suc (count_TV,bf0,b_sol,c,c_c,cfpost,g_init,gf,lp_sol,tf,npost,solP)

ti_file :: String -> IO()
ti_file fname = do
                s <- readFile fname
                ti_string s

print_simple_summary :: (Int,String,[Constrain],Map Int CSet,ContextAn,Type,Solution) -> IO()
print_simple_summary (a,tvinfo,c,c_c,gpre,t,sol) = do
              output "--------------------Analysing--------------------\n"
              output "-----Base Types----------------------------------\n"
              output ("Used_Variables: " ++ show a ++ "\n")
              output (tvinfo ++ "\n")
              output ("Generated_Constraints: " ++ show (length c) ++ "\n")
              output (show c ++ "\n" )
              output ("Closed_Constraints: " ++ show (length (Map.keys c_c)) ++ "\n")
              output (show c_c ++ "\n")
              output ("Variable_Types: " ++ show gpre ++ "\n")
              output ("Solution: " ++ show sol ++ "\n")
              output ("Result : " ++ show t ++ " :: " ++ show (type_eliminate_TVs sol t) ++ "\n")


print_summary :: ReturnCode -> (Int,Int,Int,[Constrain],Map Int CSet,[ConstrainAn],ContextAn,ContextAn,Maybe (Double, Map String Double),TypeP,Annotation,SolutionAn) -> IO()
print_summary Success (a,b_all,b_sol,c,c_c,lp_c,gpre,gpost,lp_sol,tf,nf,solP) = do
              output "--------------------Analysing--------------------\n"
              output "-----Base Types----------------------------------\n"
              output ("Used Variables : " ++ show a ++ "\n")
              output ("Generated Constraints : " ++ show (length c) ++ "\n")
              output ("Closed Constraints : " ++ show (length (Map.keys c_c)) ++ "\n")
              output "-----Annotations---------------------------------\n"
              output ("Used Variables : " ++ show b_all ++ "\n")
              output ("Generated Constraints : " ++ show (length lp_c) ++ "\n")
              output "-----Result--------------------------------------\n"
              output ("Variable Types [before execution]: \n" ++ (get_full_variable_types (var_names gpre ) gpre  (get_sol lp_sol)) ++ "\n")
              output ("Variable Types [after execution]:  \n" ++ (get_full_variable_types (var_names gpost) gpost (get_sol lp_sol)) ++ "\n")
              output ("whole program: " ++ (show (Map.lookup ("n_" ++ show b_sol) (get_sol lp_sol))) ++ "->" ++ (printSol_P tf (get_sol lp_sol)) ++ "," ++ (show (Map.lookup (show nf) (get_sol lp_sol))) ++"\n\n")
              output ("total resource need: " ++ show (get_res lp_sol) ++ "\n")
print_summary cod _ = output ("Error while solving LP:\n" ++ (show cod) ++ "\n")

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
lp a (g,b) cs |trace 2 ("Objective function includes: " ++ show g ++ " and " ++ show b) False = undefined
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
objFun a = linCombination (objFun_list a)

objFun_list :: [Int] -> [(Int,String)]
objFun_list is = Prelude.map (\i -> (1,"n_" ++ show i)) is

obj_3 :: LinFunc String Int
obj_3 = linCombination [(1,"n_0"),(1,"n_1"),(1,"n_2")]

get_full_variable_types :: [String] -> ContextAn -> Map String Double -> String
get_full_variable_types ss e m = Prelude.foldl (\a b -> (a ++ "\n" ++ b ++ ":" ++ get_full_variable_type b e m)) "" ss

get_full_variable_type :: String -> ContextAn -> Map String Double -> String
get_full_variable_type s e m = let (t,psi) = var_get e s
                               in printSol_member s (t,psi) m

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
                           Nothing -> "Variable " ++ show i ++ "not found"
printSol_Ann a _sol = show a

printSol_members :: MembersAn -> Map String Double -> String
printSol_members mem sol = "{" ++ (Map.foldWithKey (\s ty prv -> prv ++ (printSol_member s ty sol)) "" mem) ++ "}"

printSol_member :: String -> (TypeAn,FieldType) -> Map String Double -> String
printSol_member s (t,tf) sol = (show s) ++ ":" ++ (printSol_An t sol) ++ (show tf) ++ ","

printSol_An :: TypeAn -> Map String Double -> String
printSol_An (t,nu,n) sol = "(" ++ printSol_P t sol ++ "," ++ (printSol_Ann nu sol) ++ "/" ++ printSol_Ann n sol ++ ")"
