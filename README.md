AmorJiSe: An amortised type inference for JavaScript source.

Executing the type inference
----------------------------
The docker image has been uploaded to hub.docker.com with the id dfranzen/amorjise. Launch the docker with
  > docker run -it dfranzen/amorjise /bin/bash

Launch the AmorJiSe system with
  > stack ghci

Using the type inference
------------------------
The system knows the following main commands
  - ti_string: analyses JavaScript code provided as string parameter using the AmorJiSe system
  - tis_string: as ti_string, but only executes the JS_0^T analysis to compute the data-types
  - ti_file: reads and analyses a JavaScript file, provided its path using the AmorJiSe system
  - ti_test: run the test cases

The output detail is routed through the central trace method. By changing the variable trace_level in Debugging.hs the amount of output can be specified for all those commands.

Specifying the resource model:
-----------------------------
The resource model for the language activated resources is specified in Res_model.hs. For modification emacs is included in this image. Each language construct analysed by the system has one constant e.g. c_varW for writing to a variable. Once the model has been modified it can be reloaded into the haskell instance with
  > :r Res_model

The resource model for the API activated resource is specified in API_model.hs. All resource consuming APIs are specified in api_pairs. A few examples are provided. Each pair consists of the path to the API and its annotatated function type.

Examples
--------
  Resource model
  --------------
  An example resource model is included. The resource model for the language activated resources analyses heap space. Each variable declaration, object declaration, field extension and constructor invocation consumes one resource unit.
The API activated resource model considers the API "UPLOAD" as resource consuming function. Each invocation consumes one resource unit. Similar resource models for the API functions
 - navigator.geolocation.getCurrentPosition (PhoneGap GPS API)
 - navigator.notification.alert (PhoneGap message dialog API)
 - document.getEventListener (HTML even listener registration API)
 - document.getElementById (HTML DOM selection API)
 - document.getElementByTagName (HTML DOM selection API)

  JavaScript code
  ---------------
  The basic building blocks from which the analysed JavaScript scripts can be build are shown in a series of examples:
  - ti_string "34" (val) (result c_val)
  - ti_string "x" (varR) (result: "x not defined")
  - ti_string "x=4" (varW) (result: "x not defined")	
  - ti_string "var x" (varD)  (result c_varD)
  - ti_string "var x;x" (varR) (result "uninitialised variable x")
  - ti_string "var x=4" (varW) (result c_varD + c_varW + c_val)
  - ti_string "var x=4;x" (varR) (result c_varD + c_varW + c_varR + c_val + c_seq)
  - ti_string "var x;x=4" (varW) (result c_varD + c_varW + c_val + c_seq)
  - ti_string "return {m:2}" (objD) (result c_objD + c_memW + c_val)
  - ti_string "var x={m:2}" (objD) (result c_objD + c_memW(Potential) + c_val + c_varD +c_varW)
  - ti_string "var x={m:2};return x.m" (result c_objD + c_varD + c_varW + c_memW(Potential) + c_val + c_seq + c_varR + c_memR)
  
  - ti_string "var x={m:2};x.m=3" (result c_objD + c_varD + c_varW + c_memW(Potential) + c_val + c_seq + c_varR + c_memW(Potential) + c_val)
  - ti_string "var x={m:2};x.m;x.m=3" (result c_objD + c_varD + c_varW + c_memW(Potential) + c_val + c_seq + c_memR + c_seq + c_varW + c_memW(Definite) + c_val)
  - ti_string "function f(x) {x.next}" (result c_funD)
  - ti_string "function f(x) {f(x.next)};var x={next:null}; var y={next:x};f(x)" The absolute result does not make real sense, since null.next can be typed, but cannot be evaluated in the formal operational semantics. The analysis behaves correct though, since f(y) consumes 140 resources more, to execute one more iteration of f. The example also shows recursive object types and recursive functions with recursive objects as parameter types.
  - ti_string "return true?3:4" (result c_cond + c_val + c_val)