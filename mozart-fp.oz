%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 📘 FP Project – Task 1: GraphGeneration (Corrected)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Consideraciones:
%% No se puede usar palabras reservadas de mozart como fun, local, etc.

declare

%% ────────────────────────────────────────────────
%% STEP 0 – Utilities
%% ────────────────────────────────────────────────

fun {Str2Lst S}
   local
      fun {CleanChars Cs}
         case Cs
         of nil then nil
         [] C|Cr then
            if C==&( orelse C==&) orelse C==&, then
               & | {CleanChars Cr}  %% reemplaza por espacio
            else
               C | {CleanChars Cr}
            end
         end
      end
      Cleaned = {CleanChars {VirtualString.toString S}}
   in
      {Map {String.tokens Cleaned & }
         fun {$ L} {String.toAtom L} end}
   end
end

fun {FindIndex L P}
   local FindIndexAux in
      fun {FindIndexAux L P I}
         case L
         of nil then false
         [] H|T then
            if {P H} then I
            else {FindIndexAux T P I+1}
            end
         end
      end
      {FindIndexAux L P 1}
   end
end

fun {CleanTokens L}
   case L
   of nil then nil
   [] H|T then
      if H=='' then {CleanTokens T}
      else H|{CleanTokens T}
      end
   end
end

%% ────────────────────────────────────────────────
%% STEP 1 – Node constructors
%% ────────────────────────────────────────────────

fun {Leaf X}
   local S in
      S = {Atom.toString X}
      if {String.isInt S} then leaf(num:{String.toInt S})
      else leaf(var:X)
      end
   end
end

fun {App F A}
   app(function:F arg:A)
end

%% ────────────────────────────────────────────────
%% STEP 2 – Recursive expression builder
%% ────────────────────────────────────────────────
%%  e.g. ["square" "square" "3"]
%%  → app(fun:leaf(var:"square") arg:app(fun:leaf(var:"square") arg:leaf(num:3)))

fun {BuildExpr Tokens}
   case Tokens
   of nil then unit

   %% caso 1: definición interna var ... in ...
   [] 'var'|VarName|'='|Rest then
      local BindTokens BodyTokens in
         %% separar binding y cuerpo (por la palabra in)
         BindTokens = {List.takeWhile Rest fun {$ T} T \= 'in' end}
         BodyTokens = {List.dropWhile Rest fun {$ T} T \= 'in' end}
         case BodyTokens
         of 'in'|BodyRest then
            var(bindings:[bind(var:VarName expr:{BuildExpr BindTokens})]
                body:{BuildExpr BodyRest})
         else
            raise error('missing_in_keyword'(tokens:Tokens)) end
         end
      end

   %% caso 2: expresión simple (operador o valor único)
   [] [X] then {Leaf X}

   %% caso 3: aplicación binaria (función + argumento)
   [] X|Y|nil then {App {Leaf X} {Leaf Y}}

   %% caso 4: aplicación n-aria
   [] X|Rest then {App {Leaf X} {BuildExpr Rest}}
   end
end

%% ────────────────────────────────────────────────
%% STEP 3 – Full program graph generator
%% ────────────────────────────────────────────────

fun {GraphGeneration ProgramStr}
   local
      Lines TokensDef TokensCall FName ArgsTokens BodyTokens FunBody CallGraph
   in
      Lines = {String.tokens ProgramStr &\n}

      if {Length Lines} < 2 then
         raise error('Program must have two lines: definition and call') end
      end

      TokensDef  = {CleanTokens {Str2Lst {List.nth Lines 1}}}
      TokensCall = {CleanTokens {Str2Lst {List.nth Lines 2}}}

      %% expect "function <name> <arg1> <arg2> ... = <body>"
      if {List.nth TokensDef 1} \= function then
         raise error('Definition must start with function') end
      end

      FName = {List.nth TokensDef 2}

      %% separa argumentos de la parte derecha
      local EqPos in
         EqPos = {FindIndex TokensDef fun {$ X} X=='=' end}
         if EqPos == false then
            raise error('Missing "=" in definition') end
         end
         ArgsTokens = {List.drop {List.take TokensDef (EqPos-1)} 2}
         BodyTokens = {List.drop TokensDef EqPos}
      end

      FunBody   = {BuildExpr BodyTokens}
      CallGraph = {BuildExpr TokensCall}

      prog(function:FName args:ArgsTokens body:FunBody call:CallGraph)
   end
end

%% ────────────────────────────────────────────────
%% STEP 4 – Pretty Printing Functions
%% ────────────────────────────────────────────────

proc {PrintProgram Prog}
   {System.showInfo "=== PROGRAM GRAPH ==="}
   {System.showInfo "Function: "#{Value.toVirtualString Prog.function 0 0}}
   {System.showInfo "Arguments: "#{Value.toVirtualString Prog.args 0 0}}
   {System.showInfo "Body: "#{Value.toVirtualString Prog.body 0 0}}
   {System.showInfo "Call: "#{Value.toVirtualString Prog.call 0 0}}
   {System.showInfo ""}
end

proc {PrintRedex R}
   {System.showInfo "=== REDEX ANALYSIS ==="}
   {System.showInfo "Status: "#{Value.toVirtualString R.status 0 0}}
   {System.showInfo "Kind: "#{Value.toVirtualString R.kind 0 0}}
   {System.showInfo "Head: "#{Value.toVirtualString R.head 0 0}}
   {System.showInfo "Arity: "#{Value.toVirtualString R.arity 0 0}}
   if {HasFeature R args} then
      {System.showInfo "Args: "#{Value.toVirtualString R.args 0 0}}
   end
   if {HasFeature R rest} then
      {System.showInfo "Rest: "#{Value.toVirtualString R.rest 0 0}}
   end
   {System.showInfo "All Args: "#{Value.toVirtualString R.allargs 0 0}}
   {System.showInfo "Apps: "#{Value.toVirtualString R.apps 0 0}}
   {System.showInfo ""}
end

proc {PrintResult R}
   {System.showInfo "=== RESULT ==="}
   {System.showInfo "Final Value: "#{Value.toVirtualString R 0 0}}
   {System.showInfo "========================================="}
   {System.showInfo ""}
end

%% ────────────────────────────────────────────────
%% STEP 5 – Tests
%% ────────────────────────────────────────────────

local G1 G2 in
   {System.showInfo "TEST 1: square square 3"}
   G1 = {GraphGeneration "function square x = x * x\nsquare square 3"}
   {PrintProgram G1}

   {System.showInfo "TEST 2: twice 5"}
   G2 = {GraphGeneration "function twice x = x + x\ntwice 5"}
   {PrintProgram G2}
end


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 📘 FP Project – Task 2: NextReduction
%%  - Encuentra la redex externa (outermost) para reducir
%%  - Si faltan argumentos → WHNF
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% ¿Es operador primitivo?
fun {IsPrimitive Op}
    {List.member Op ['+' '-' '*' '/']}
 end
 
 %% Aridad de la "cabeza" (head) según sea primitiva o supercombinator
 fun {HeadArity Head Prog}
    case Head
    of leaf(var:Op) then
       if {IsPrimitive Op} then 2
       elseif Op==Prog.function then 1      %% tu minilenguaje: 1 parámetro
       else 0                                %% variable libre / desconocida
       end
    [] leaf(num:_) then 0
    else 0
    end
 end
 
 %% Clasificación (para informar el tipo de redex)
 fun {HeadKind Head Prog}
    case Head
    of leaf(var:Op) then
       if {IsPrimitive Op} then primitive(Op)
       elseif Op==Prog.function then supercombinator(Op)
       else variable(Op)
       end
    [] leaf(num:N) then number(N)
    else other
    end
 end
 
 %% Unwind: sigue la rama izquierda acumulando:
 %%   - args: lista de argumentos encontrados (primero el más cercano a la cabeza)
 %%   - apps: lista de nodos app en orden de arriba hacia abajo (raíz→fondo)
 fun {Unwind Expr Args Apps}
    case Expr
    of app(function:F arg:A) then
       {Unwind F A|Args Expr|Apps}
    else
       unwind(head:Expr args:Args apps:Apps)
    end
 end
 
 %% Acceso seguro al enésimo (1-indexed)
 fun {Nth L I}
    {List.nth L I}
 end
 
%% NextReduction:
%%  Entrada: prog(function: FName args: ... body: ... call: CallGraph)
 %%  Salida:  record con la info de la redex externa
 %%           redex(kind:primitive/supercombinator/..., head:Head,
 %%                 arity:K, args:ArgsK, rest:RemainingArgs,
 %%                 root:RootAppNode, apps:SpineApps, allargs:AllArgs,
 %%                 status:ok|whnf|stuck)
 fun {NextReduction Prog}
    local UW Head K Apps AllArgs LenApps RootIndex ArgsK Remaining Kind in
       UW      = {Unwind Prog.call nil nil}
       Head    = UW.head
       AllArgs = UW.args           %% orden: [arg1, arg2, ...] donde arg1 es el más cercano a la cabeza
       Apps    = UW.apps           %% orden: raíz → fondo
       K       = {HeadArity Head Prog}
       Kind    = {HeadKind Head Prog}
 
       if K==0 then
          %% No hay redex (cabeza no reducible)
          redex(status:stuck kind:Kind head:Head allargs:AllArgs apps:Apps)
       elseif {Length AllArgs} < K then
          %% No hay suficientes argumentos → WHNF
          redex(status:whnf kind:Kind head:Head arity:K allargs:AllArgs apps:Apps)
       else
          %% Hay redex externa: tomar K args y ubicar el nodo raíz correspondiente
          ArgsK     = {List.take AllArgs K}          %% primeros K argumentos
          Remaining = {List.drop AllArgs K}
          LenApps   = {Length Apps}
          RootIndex = LenApps - K + 1                %% nodo app que es raíz de la redex
          redex(status:ok kind:Kind head:Head arity:K
                args:ArgsK rest:Remaining
                root:{Nth Apps RootIndex}
                apps:Apps allargs:AllArgs)
       end
    end
 end
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 🔬 Tests de Task 2
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

local P1 R1 P2 R2 P3 R3 in
   {System.showInfo "TASK 2: NextReduction Tests"}
   {System.showInfo "========================================="}
   
   %% square square 3
   {System.showInfo "TEST 1: square square 3"}
   P1 = {GraphGeneration "function square x = x * x\nsquare square 3"}
   R1 = {NextReduction P1}
   {PrintProgram P1}
   {PrintRedex R1}

   %% twice 5
   {System.showInfo "TEST 2: twice 5"}
   P2 = {GraphGeneration "function twice x = x + x\ntwice 5"}
   R2 = {NextReduction P2}
   {PrintProgram P2}
   {PrintRedex R2}

   %% + 2 (falta arg) → WHNF sobre primitiva
   {System.showInfo "TEST 3: + 2 (missing argument → WHNF)"}
   P3 = prog(function:'f' args:[x]
             body:leaf(var:x)
             call:app(function:leaf(var:'+') arg:leaf(num:2)))
   R3 = {NextReduction P3}
   {PrintProgram P3}
   {PrintRedex R3}
end
 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 📘 FP Project – Task 3: Reduce (outermost one-step)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Reusa IsPrimitive, NextReduction, etc. definidos en Task 2

%% -------- Helpers --------

%% Sustitución: reemplaza todas las ocurrencias de Var por WithNode
fun {Subst Expr Var WithNode}
   case Expr
   of leaf(var:V) then
      if V==Var then WithNode else Expr end
   [] leaf(num:_) then
      Expr
   [] app(function:F arg:A) then
      app(function:{Subst F Var WithNode}
          arg:      {Subst A Var WithNode})
   [] var(bindings:Bs body:B) then
      %% Para variables internas, sustituir en el cuerpo pero no en los bindings
      var(bindings:Bs body:{Subst B Var WithNode})
   else
      Expr
   end
end

%% Aplica argumentos restantes (si los hubiera) a un nodo (asocia a la izquierda)
fun {ApplyRest Node Rest}
   case Rest
   of nil        then Node
   [] R|Rs then {ApplyRest app(function:Node arg:R) Rs}
   end
end

%% Evalúa variables internas (var ... in ...)
fun {EvalVarBindings Bindings Prog}
   case Bindings
   of nil then Prog
   [] bind(var:V expr:E)|Rest then
      %% Evaluar la expresión E hasta obtener un valor
      local EvaluatedE in
         EvaluatedE = {EvalToNum E Prog}
         %% Sustituir V por el valor evaluado en el resto de bindings y en Prog
         local NewRest NewProg in
            NewRest = {Map Rest fun {$ B} 
               bind(var:B.var expr:{Subst B.expr V leaf(num:EvaluatedE)})
            end}
            NewProg = {Subst Prog V leaf(num:EvaluatedE)}
            {EvalVarBindings NewRest NewProg}
         end
      end
   end
end

%% Reemplaza una subexpresión (Root) por New dentro de Expr
fun {ReplaceSub Expr Root New}
   if Expr==Root then
      New
   else
      case Expr
      of app(function:F arg:A) then
         app(function:{ReplaceSub F Root New}
             arg:      {ReplaceSub A Root New})
      else
         Expr
      end
   end
end

%% Evalúa una subexpresión hasta número usando una pequeña "máquina"
%%   (vuelve a usar NextReduction + Reduce sobre un programa temporal)
fun {EvalToNum Expr Prog}
   case Expr
   of leaf(num:N) then N
   [] var(bindings:Bs body:B) then
      %% Evaluar variables internas primero
      local EvaluatedBody in
         EvaluatedBody = {EvalVarBindings Bs B}
         {EvalToNum EvaluatedBody Prog}
      end
   else
      local P R P2 in
         P  = prog(function:Prog.function args:Prog.args body:Prog.body call:Expr)
         R  = {NextReduction P}
         if R.status==ok then
            P2 = {Reduce P}
            {EvalToNum P2.call P2}
         else
            raise error('expected_number'(expr:Expr status:R.status)) end
         end
      end
   end
end

%% -------- Task 3: Reduce (one outermost step) --------

fun {Reduce Prog}
   local R NewNode NewCall in
      R = {NextReduction Prog}
      if R.status \= ok then
         %% No hay redex (WHNF o atascado) → no cambia
         Prog
      else
         case R.kind
         of supercombinator(Fn) then
            %% Instanciar cuerpo con TODOS los argumentos consumidos
            local SubstAll in
               fun {SubstAll Expr ArgsNames ArgsValues}
                  case ArgsNames
                  of nil then Expr
                  [] Name|RestNames then
                     case ArgsValues
                     of Value|RestValues then
                        {SubstAll {Subst Expr Name Value} RestNames RestValues}
                     [] nil then Expr  %% Si no hay más valores, devolver la expresión
                     end
                  end
               end
               local Instanced in
                  Instanced = {SubstAll Prog.body Prog.args R.args}
                  %% si hay más argumentos en la aplicación externa, reaplícalos
                  NewNode = {ApplyRest Instanced R.rest}
               end
            end            
         [] primitive(Op) then
            %% Evaluar ambos argumentos a número y calcular
            local A1 A2 N1 N2 Res in
               A1 = {List.nth R.args 1}
               A2 = {List.nth R.args 2}
               N1 = {EvalToNum A1 Prog}
               N2 = {EvalToNum A2 Prog}
               Res =
                  case Op
                  of '+' then N1+N2
                  [] '-' then N1-N2
                  [] '*' then N1*N2
                  [] '/' then N1 div N2   %% entero (ajústalo si quieres real)
                  end
               NewNode = {ApplyRest leaf(num:Res) R.rest}
            end
         else
            %% variable/number/other en cabeza: no reducible (debería no ocurrir con status ok)
            NewNode = R.head
         end

         %% Insertar NewNode en el árbol: reemplazar la raíz de la redex
         NewCall = {ReplaceSub Prog.call R.root NewNode}
         prog(function:Prog.function args:Prog.args body:Prog.body call:NewCall)
      end
   end
end

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 🔬 Tests Task 3
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

local P1 S1 P2 S2 S2_2 P3 S3 in
   {System.showInfo "TASK 3: Reduce (One Step) Tests"}
   {System.showInfo "========================================="}
   
   %% 1) (square square) 3 → ( (square 3) * (square 3) )
   {System.showInfo "TEST 1: (square square) 3 → ( (square 3) * (square 3) )"}
   P1 = {GraphGeneration "function square x = x * x\nsquare square 3"}
   S1 = {Reduce P1}
   {PrintProgram P1}
   {System.showInfo "After one reduction:"}
   {PrintProgram S1}

   %% 2) (twice 5) → (5 + 5) y una segunda reducción (primitiva)
   {System.showInfo "TEST 2: (twice 5) → (5 + 5) → 10"}
   P2 = {GraphGeneration "function twice x = x + x\ntwice 5"}
   S2 = {Reduce P2}
   S2_2 = {Reduce S2}
   {PrintProgram P2}
   {System.showInfo "After first reduction:"}
   {PrintProgram S2}
   {System.showInfo "After second reduction:"}
   {PrintProgram S2_2}

   %% 3) (+ 2 3) → 5
   {System.showInfo "TEST 3: (+ 2 3) → 5"}
   P3 = prog(function:'f' args:[x] body:leaf(var:x)
             call:app(function:app(function:leaf(var:'+') arg:leaf(num:2))
                           arg:leaf(num:3)))
   S3 = {Reduce P3}
   {PrintProgram P3}
   {System.showInfo "After reduction:"}
   {PrintProgram S3}
end


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 📘 FP Project – Task 4: Evaluate (iterative full reduction)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fun {Evaluate Prog}
   local R Pnext in
      R = {NextReduction Prog}
      if R.status == ok then
         %% hay redex → reduce y continúa
         Pnext = {Reduce Prog}
         {Evaluate Pnext}
      elseif R.status == whnf then
         %% forma normal débil: verificar si hay variables internas que evaluar
         case Prog.call
         of var(bindings:Bs body:B) then
            %% Evaluar variables internas
            local EvaluatedBody in
               EvaluatedBody = {EvalVarBindings Bs B}
               case EvaluatedBody
               of leaf(num:N) then N
               [] _ then
                  %% Crear nuevo programa con el cuerpo evaluado y continuar
                  local NewProg in
                     NewProg = prog(function:Prog.function args:Prog.args body:Prog.body call:EvaluatedBody)
                     {Evaluate NewProg}
                  end
               end
            end
         [] _ then
            %% No es var, devolver el grafo
            Prog
         end
      else
         %% stuck o sin redex: devolver el valor si es número
         case Prog.call
         of leaf(num:N) then N
         [] _ then Prog
         end
      end
   end
end

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 🔬 Tests Task 4
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

local P1 R1 P2 R2 in
   {System.showInfo "TASK 4: Evaluate (Full Reduction) Tests"}
   {System.showInfo "========================================="}
   
   %% Ejemplo 1 — square square 3 → 81
   {System.showInfo "TEST 1: square square 3 → 81"}
   P1 = {GraphGeneration "function square x = x * x\nsquare square 3"}
   R1 = {Evaluate P1}
   {PrintProgram P1}
   {PrintResult R1}

   %% Ejemplo 2 — fourtimes 2 → 8
   %% (extiende lenguaje: var y = x*x in y+y)
   %% Se comportará igual que (x*x)+(x*x)
   {System.showInfo "TEST 2: fourtimes 2 → 8"}
   P2 = {GraphGeneration "function fourtimes x = x * x + x * x\nfourtimes 2"}
   R2 = {Evaluate P2}
   {PrintProgram P2}
   {PrintResult R2}
end



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 🔬 Tests: Extended Language
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

local P1 P2 P3 in
   {System.showInfo "EXTENDED LANGUAGE Tests"}
   {System.showInfo "========================================="}
   
   %% Múltiples parámetros
   {System.showInfo "TEST 1: Multiple parameters - sum_n 1 1 1 2 → 6"}
   P1 = {GraphGeneration "function sum_n x y z n = (x + y + z) * n\nsum_n 1 1 1 2"}
   {PrintProgram P1}
   {PrintResult {Evaluate P1}}

   %% Variable interna
   {System.showInfo "TEST 2: Internal variables - var_use 2 → 5"}
   P2 = {GraphGeneration "function var_use x = var y = x * x in var z = y * 2 in z - 3\nvar_use 2"}
   {PrintProgram P2}
   {PrintResult {Evaluate P2}}

   %% Nesting complejo
   {System.showInfo "TEST 3: Complex nesting - arithmetic with nested calls"}
   P3 = {GraphGeneration "function arithmetic x y = ((x + y) / (x - y)) * 2\narithmetic arithmetic 5 6 arithmetic 2 11"}
   {PrintProgram P3}
   {PrintResult {Evaluate P3}}
end


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 🔬 Tests: Edge Cases for Robustness
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

local P1 P2 P3 P4 P5 P6 P7 P8 in
   {System.showInfo "EDGE CASE TESTS"}
   {System.showInfo "========================================="}

   %% 1️⃣ Identity function
   {System.showInfo "TEST 1: fun id x = x\nid 5 → 5"}
   P1 = {GraphGeneration "function id x = x\nid 5"}
   {PrintProgram P1}
   {PrintResult {Evaluate P1}}

   %% 2️⃣ Constant function (ignores second argument)
   {System.showInfo "TEST 2: fun const x y = x\nconst 5 9 → 5"}
   P2 = {GraphGeneration "function const x y = x\nconst 5 9"}
   {PrintProgram P2}
   {PrintResult {Evaluate P2}}

   %% 3️⃣ Nested parentheses in arithmetic expression
   {System.showInfo "TEST 3: fun nested x = x + (x * x)\nnested 3 → 12"}
   P3 = {GraphGeneration "function nested x = x + (x * x)\nnested 3"}
   {PrintProgram P3}
   {PrintResult {Evaluate P3}}

   %% 4️⃣ Multi-parameter addition and repetition
   {System.showInfo "TEST 4: fun doubleadd x y = (x + y) + (x + y)\ndoubleadd 2 3 → 10"}
   P4 = {GraphGeneration "function doubleadd x y = (x + y) + (x + y)\ndoubleadd 2 3"}
   {PrintProgram P4}
   {PrintResult {Evaluate P4}}

   %% 5️⃣ Variable chaining with var-in nesting
   {System.showInfo "TEST 5: fun var_chain x = var y = x + 1 in var z = y * 2 in z + y\nvar_chain 2 → 9"}
   P5 = {GraphGeneration "function var_chain x = var y = x + 1 in var z = y * 2 in z + y\nvar_chain 2"}
   {PrintProgram P5}
   {PrintResult {Evaluate P5}}

   %% 6️⃣ Complex nested function calls
   {System.showInfo "TEST 6: fun complex x = (x * x) + (x * x)\ncomplex 3 → 18"}
   P6 = {GraphGeneration "function complex x = (x * x) + (x * x)\ncomplex 3"}
   {PrintProgram P6}
   {PrintResult {Evaluate P6}}

   %% 7️⃣ Multiple parameters with complex expressions
   {System.showInfo "TEST 7: fun mult x y z = (x + y) * z\nmult 2 3 4 → 20"}
   P7 = {GraphGeneration "function mult x y z = (x + y) * z\nmult 2 3 4"}
   {PrintProgram P7}
   {PrintResult {Evaluate P7}}

   %% 8️⃣ Free variable (non-reducible WHNF)
   {System.showInfo "TEST 8: fun bad x = x + y\nbad 3 → WHNF (y unknown)"}
   P8 = {GraphGeneration "function bad x = x + y\nbad 3"}
   {PrintProgram P8}
   {PrintResult {Evaluate P8}}
end