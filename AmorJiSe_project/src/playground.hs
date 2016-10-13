import Language.JavaScript.Parser.Parser
import Language.JavaScript.Parser.AST
import Language.JavaScript.Parser.SrcLocation

import Data.Map as Map
import Data.Set as Set

import Conditionals
import Extraction

import ConstGen
import JST0_context

--import Extraction

parser :: String -> IO()
parser s = do
  putStr (show (parse s "test.js"))

main ::IO()
main = putStr "blubb"