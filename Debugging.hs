module Debugging where

import Debug.Trace

-- 1: errors
-- 2: Temporary Debug output
-- 5: Analysis steps
-- 10: Rules
-- 20: Main Analysis functions
-- 25: Constraints Analysis steps, minor Analysis steps
-- 30: Aux_Functions
traceLevel :: Int
traceLevel = 2

trace :: Int -> String -> Bool -> Bool
trace l a b |(l == 1) && Debug.Trace.trace ("****ERROR****" ++ a) True = undefined
trace l a b |(l == 10) && (traceLevel>=10) = Debug.Trace.trace ("\n-->>" ++ a) b
trace l a b |(l == 25) && (traceLevel>=25) = Debug.Trace.trace ("CI " ++ a) b
trace l a b |(l>1) && (traceLevel>=l) = Debug.Trace.trace a b
trace _ _ b = b

errorOut :: String -> Bool -> Bool
errorOut a b = Debug.Trace.trace a b
