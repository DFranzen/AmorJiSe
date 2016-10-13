module API_model where

import JST0P_context
import JST0P_types
import JST0_type_aux

init_context :: ContextAn
init_context = let
  (ps,ts) = apis
  g = JST0P_context.empty_empty
  in var_create_path_list g ps ts

apis :: ([Path],[(TypeAn,FieldType)])
apis = lp2pl api_pairs

api_pairs :: [(Path,TypeP)]
api_pairs = [
    (["UPLOAD"],JST0P_Function objectAn_empty [(JST0P_Int,I 0,I 0)] (I 1) (JST0P_Int,I 0,I 0) (I 0))
    ]
--  (["navigator","geolocation","getCurrentPosition"],function_getCurrentPosition),
--  (["navigator","notification","alert"],function_alert),
--  (["document","addEventListener"],function_addEventListener),
--  (["document","getElementById"],
--  JST0P_Function objectAn_empty [(JST0P_String "",I 0,I 0)] (I 0) (object_DOM_element,I 0,I 0) (I 0)),
--  (["document","getElementByTagName"],
--   JST0P_Function objectAn_empty [(JST0P_String "",I 0,I 0)] (I 0) (object_HTMLCollection,I 0,I 0) (I 0)),
-- (["parseInt"],JST0P_Function objectAn_empty [(JST0P_String "",I 0,I 0)] (I 0) (JST0P_Int,I 0,I 0) (I 0))
--  ]

lp2pl :: [(Path,TypeP)] -> ([Path],[(TypeAn,FieldType)])
lp2pl [] = ([],[])
lp2pl (p:ps) = let
  (ss,ts) = lp2pl ps
  (s,t) = p
  in (s:ss,((t,I 0,I 0),Definite):ts) -- The resource consuming function can never store any resources


-- Model a DOM element
-- Contains the following DOM API methods
--   - addEventListener
-- Contains the following Properties:
--   - onclick: EventCallback function
object_DOM_element :: TypeP
object_DOM_element = let
  ael = function_addEventListener
  oc = function_eventCallback
  in objectP_from_list_ft NotRec [("addEventListener",(ael,I 0,I 0),Definite),
                                  ("onclick",(oc,I 0,I 0),Potential),
                                  ("width",(JST0P_String "",I 0,I 0),Definite)]

object_HTMLCollection :: TypeP
object_HTMLCollection = let
  fitem = JST0P_Function objectAn_empty [(JST0P_Int,I 0,I 0)] (I 0) (object_DOM_element,I 0,I 0) (I 0)
  in objectP_from_list_ft NotRec [("length",(JST0P_Int,I 0,I 0),Definite),("item",(fitem,I 0,I 0),Definite)]

-- function type for the addEventListener
-- no resources consumed
-- Arguments:
--   - String (Event)
--   - Callback Function for this event
--   - Bool (Capture, dipatch here fist before bubbeling down)
function_addEventListener :: TypeP
function_addEventListener = JST0P_Function
        objectAn_empty
        [(JST0P_String "",I 0,I 0),(function_eventCallback,I 0,I 0),(JST0P_Bool,I 0,I 0)]
        (I 0)
        (JST0P_None,I 0,I 0)
        (I 0)

-- function type for an empty event callback function
-- no arguments, this is empty, no resources used
function_eventCallback :: TypeP
function_eventCallback = JST0P_Function objectAn_empty [] (I 0) (JST0P_None,I 0,I 0) (I 0)

-- function type for the getCurrentPosition function
-- consume one unit
function_getCurrentPosition :: TypeP
function_getCurrentPosition = JST0P_Function
     objectAn_empty
     [(JST0P_Function objectAn_empty [(JST0P_Int,I 0,I 0)] (I 0) (JST0P_None,I 0,I 0) (I 0),I 0,I 0),
      (JST0P_Function objectAn_empty [(JST0P_Int,I 0,I 0)] (I 0) (JST0P_None,I 0,I 0) (I 0),I 0,I 0)]
     (I 1)
     (JST0P_None,I 0,I 0)
     (I 0) 

-- function type for navigator.notification.alert
-- Arguments:
--   - String (Message)
--   - Callback to be triggered, when Dialog is dismissed
-- Empty receiver, no resources consumed
function_alert :: TypeP
function_alert = JST0P_Function
     objectAn_empty
     [(JST0P_String "",I 0,I 0),
      (JST0P_Function objectAn_empty [] (I 0) (JST0P_None,I 0,I 0) (I 0),I 0,I 0)]
     (I 0)
     (JST0P_None,I 0,I 0)
     (I 0) 
