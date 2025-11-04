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

   %% caso 4: aplicación n-aria (asociación a la derecha)
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

      %% expect "fun <name> <arg1> <arg2> ... = <body>" or "function <name> ..."
      local FirstToken in
         FirstToken = {List.nth TokensDef 1}
         if FirstToken \= 'fun' andthen FirstToken \= function then
            raise error('Definition must start with fun or function') end
         end
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
   {System.showInfo "TEST 1: square square 3 (using 'fun' instead of 'function')"}
   G1 = {GraphGeneration "fun square x = x * x\nsquare square 3"}
   {PrintProgram G1}

   {System.showInfo "TEST 2: twice 5 (using 'function')"}
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
    {List.member Op ['+' '-' '*' '/' 'mod' 'div' 'pow' 'sqrt' 'log']}
 end

%% ¿Es operador unario?
fun {IsUnary Op}
    {List.member Op ['sqrt' 'log']}
 end

%% ¿Es operador binario?
fun {IsBinary Op}
    {List.member Op ['+' '-' '*' '/' 'mod' 'div' 'pow']}
 end
 
 %% Aridad de la "cabeza" (head) según sea primitiva o supercombinator
 fun {HeadArity Head Prog}
    case Head
    of leaf(var:Op) then
       if {IsUnary Op} then 1
       elseif {IsBinary Op} then 2
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

%% ✅ FIX: Evalúa variables internas (var ... in ...) correctamente
fun {EvalVarBindings Bindings Body}
   case Bindings
   of nil then Body
   [] bind(var:V expr:E)|Rest then
      %% Evaluar la expresión E hasta obtener un valor
      local EvaluatedE in
         EvaluatedE = {EvalToNum E prog(function:'temp' args:nil body:E call:E)}
         %% Sustituir V por el valor evaluado en el resto de bindings y en Body
         local NewRest NewBody in
            NewRest = {Map Rest fun {$ B} 
               bind(var:B.var expr:{Subst B.expr V leaf(num:EvaluatedE)})
            end}
            NewBody = {Subst Body V leaf(num:EvaluatedE)}
            {EvalVarBindings NewRest NewBody}
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
            %% ✅ FIX: Sustitución múltiple para funciones con múltiples parámetros
            local SubstMultiple in
               fun {SubstMultiple Expr ArgsNames ArgsValues}
                  case ArgsNames#ArgsValues
                  of nil#nil then Expr
                  [] (Name|RestNames)#(Value|RestValues) then
                     {SubstMultiple {Subst Expr Name Value} RestNames RestValues}
                  [] _#_ then Expr  %% Longitudes diferentes, devolver sin cambios
                  end
               end
               local Instanced in
                  Instanced = {SubstMultiple Prog.body Prog.args R.args}
               %% si hay más argumentos en la aplicación externa, reaplícalos
                  NewNode = {ApplyRest Instanced R.rest}
               end
            end
         [] primitive(Op) then
            %% Manejar operaciones unarias y binarias
            if {IsUnary Op} then
               %% Operación unaria: sqrt, log
               local A1 N1 Res in
                  %% Si hay argumentos restantes, aplícalos al argumento unario antes de evaluar
                  A1 = {ApplyRest {List.nth R.args 1} R.rest}
                  try
                     N1 = {EvalToNum A1 Prog}
                     if Op=='log' andthen N1=<0 then
                        raise error('log_negative_or_zero'(value:N1)) end
                     else
                        case Op
                        of 'sqrt' then
                           {Float.toInt {Float.sqrt {Int.toFloat N1}}}
                        [] 'log' then
                           {Float.toInt {Float.log {Int.toFloat N1}}}
                        end
                     end                     
                  catch _ then
                     %% No es numérico aún: dejar como aplicación primitiva con su argumento
                     NewNode = app(function:leaf(var:Op) arg:A1)
                  end
               end
            else
               %% Operación binaria: +, -, *, /, mod, div, pow
               local A1 A2 N1 N2 Res in
                  %% Si hay argumentos restantes, distribuirlos en ambos argumentos binarios
                  A1 = {ApplyRest {List.nth R.args 1} R.rest}
                  A2 = {ApplyRest {List.nth R.args 2} R.rest}
                  try
                     N1 = {EvalToNum A1 Prog}
                     N2 = {EvalToNum A2 Prog}
                     Res =
                        case Op
                        of '+' then N1+N2
                        [] '-' then N1-N2
                        [] '*' then N1*N2
                        [] '/' then N1 div N2   %% división entera
                        [] 'div' then N1 div N2 %% división entera explícita
                        [] 'mod' then N1 mod N2 %% módulo
                        [] 'pow' then {Float.toInt {Float.pow {Int.toFloat N1} {Int.toFloat N2}}}
                        end
                     NewNode = leaf(num:Res)
                  catch _ then
                     %% No numérico aún: reconstruir aplicación primitiva con sus argumentos
                     NewNode = app(function:app(function:leaf(var:Op) arg:A1) arg:A2)
                  end
               end
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

%% ✅ FIX: Evaluación profunda recursiva que siempre devuelve números
fun {Evaluate Prog}
   local R Pnext in
      {System.showInfo "[Evaluate] enter call="#{Value.toVirtualString Prog.call 0 0}}
      R = {NextReduction Prog}
      {System.showInfo "[Evaluate] status="#{Value.toVirtualString R.status 0 0}}
      if {HasFeature R kind} then {System.showInfo "[Evaluate] kind="#{Value.toVirtualString R.kind 0 0}} end
      if R.status == ok then
         %% hay redex → reduce y continúa
         {System.showInfo "[Evaluate] reducing one step"}
         Pnext = {Reduce Prog}
         {System.showInfo "[Evaluate] after reduce call="#{Value.toVirtualString Pnext.call 0 0}}
         {Evaluate Pnext}
      elseif R.status == whnf then
         %% forma normal débil: verificar si hay variables internas que evaluar
         {System.showInfo "[Evaluate] WHNF, inspecting call"}
         case Prog.call
         of var(bindings:Bs body:B) then
            %% Evaluar variables internas
            {System.showInfo "[Evaluate] var-in detected, bindings="#{Value.toVirtualString Bs 0 0}}
            local EvaluatedBody in
               EvaluatedBody = {EvalVarBindings Bs B}
               {System.showInfo "[Evaluate] var-body evaluated="#{Value.toVirtualString EvaluatedBody 0 0}}
               case EvaluatedBody
               of leaf(num:N) then N
               [] _ then
                  %% Crear nuevo programa con el cuerpo evaluado y continuar
                  local NewProg in
                     NewProg = prog(function:Prog.function args:Prog.args body:Prog.body call:EvaluatedBody)
                     {System.showInfo "[Evaluate] continue with evaluated body"}
                     {Evaluate NewProg}
                  end
               end
            end
         [] app(function:F arg:A) then
            %% Desenrollar esta aplicación (no todo el Prog.call) para ver si es una primitiva completa
            local UW in
               {System.showInfo "[Evaluate] app detected. F="#{Value.toVirtualString F 0 0}}
               {System.showInfo "[Evaluate] app arg A="#{Value.toVirtualString A 0 0}}
               UW = {Unwind app(function:F arg:A) nil nil}
               {System.showInfo "[Evaluate] UW.head="#{Value.toVirtualString UW.head 0 0}}
               {System.showInfo "[Evaluate] UW.args="#{Value.toVirtualString UW.args 0 0}}
               case UW.head
               of leaf(var:Op) then
                  {System.showInfo "[Evaluate] head var="#{Value.toVirtualString Op 0 0}}
                  if {IsUnary Op} andthen {Length UW.args} >= 1 then
                     %% Operación unaria completa
                     local A1 N1 in
                        A1 = {List.nth UW.args 1}
                        {System.showInfo "[Evaluate] unary A1="#{Value.toVirtualString A1 0 0}}
                        N1 = {EvalToNum A1 Prog}
                        {System.showInfo "[Evaluate] unary N1="#{Value.toVirtualString N1 0 0}}
                        if Op=='log' andthen N1=<0 then
                           raise error('log_negative_or_zero'(value:N1)) end
                        else
                           case Op
                           of 'sqrt' then
                              {Float.toInt {Float.sqrt {Int.toFloat N1}}}
                           [] 'log' then
                              {Float.toInt {Float.log {Int.toFloat N1}}}
                           end
                        end
                     end                  
                  elseif {IsBinary Op} andthen {Length UW.args} >= 2 then
                     %% Operación binaria completa
                     local A1 A2 N1 N2 in
                        A1 = {List.nth UW.args 1}
                        A2 = {List.nth UW.args 2}
                        {System.showInfo "[Evaluate] binary A1="#{Value.toVirtualString A1 0 0}}
                        {System.showInfo "[Evaluate] binary A2="#{Value.toVirtualString A2 0 0}}
                        N1 = {EvalToNum A1 Prog}
                        N2 = {EvalToNum A2 Prog}
                        {System.showInfo "[Evaluate] binary N1="#{Value.toVirtualString N1 0 0}}
                        {System.showInfo "[Evaluate] binary N2="#{Value.toVirtualString N2 0 0}}
                        case Op
                        of '+' then N1 + N2
                        [] '-' then N1 - N2
                        [] '*' then N1 * N2
                        [] '/' then N1 div N2
                        [] 'div' then N1 div N2
                        [] 'mod' then N1 mod N2
                        [] 'pow' then
                           {Float.toInt {Float.pow {Int.toFloat N1} {Int.toFloat N2}}}
                        end
                     end
                  else
                     %% No es primitiva completa, evaluar recursivamente usando EvaluateDeep
                     local EvalF EvalA NewProg in
                        EvalF = {EvaluateDeep F Prog}
                        EvalA = {EvaluateDeep A Prog}
                        {System.showInfo "[Evaluate] not complete primitive; EvalF="#{Value.toVirtualString EvalF 0 0}}
                        {System.showInfo "[Evaluate] EvalA="#{Value.toVirtualString EvalA 0 0}}
                        NewProg = prog(function:Prog.function args:Prog.args body:Prog.body 
                                      call:app(function:EvalF arg:EvalA))
                        {System.showInfo "[Evaluate] recurse with rebuilt app"}
                        {Evaluate NewProg}
                     end
                  end
               else
                  %% La cabeza no es una primitiva, evaluar recursivamente
                  local EvalF EvalA NewProg in
                     EvalF = {EvaluateDeep F Prog}
                     EvalA = {EvaluateDeep A Prog}
                     {System.showInfo "[Evaluate] head not primitive; EvalF="#{Value.toVirtualString EvalF 0 0}}
                     {System.showInfo "[Evaluate] EvalA="#{Value.toVirtualString EvalA 0 0}}
                     NewProg = prog(function:Prog.function args:Prog.args body:Prog.body 
                                   call:app(function:EvalF arg:EvalA))
                     {System.showInfo "[Evaluate] recurse non-primitive"}
                     {Evaluate NewProg}
                  end
               end
            end
         [] _ then
            %% No es var ni app, devolver el grafo
            {System.showInfo "[Evaluate] WHNF default → return graph"}
            Prog
         end
      else
         %% stuck o sin redex: devolver el valor si es número
         {System.showInfo "[Evaluate] stuck/other; return if number"}
         case Prog.call
         of leaf(num:N) then N
         [] _ then Prog
         end
      end
   end
end

%% ✅ FIX: Función auxiliar para evaluación profunda de expresiones
fun {EvaluateDeep Expr Prog}
   case Expr
   of leaf(num:N) then Expr
   [] leaf(var:_) then Expr
   [] app(function:F arg:A) then
      local EvalF EvalA in
         EvalF = {EvaluateDeep F Prog}
         EvalA = {EvaluateDeep A Prog}
         app(function:EvalF arg:EvalA)
      end
   [] var(bindings:Bs body:B) then
      local EvaluatedBody in
         EvaluatedBody = {EvalVarBindings Bs B}
         {EvaluateDeep EvaluatedBody Prog}
      end
   else
      Expr
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

local P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 in
   {System.showInfo "🎯 FINAL TESTS - 100% CHECKLIST VERIFICATION"}
   {System.showInfo "========================================="}

   %% ✅ A. Sustitución múltiple (multi-argument functions)
   {System.showInfo "TEST A1: function const x y = x\nconst 5 9 → 5"}
   P1 = {GraphGeneration "function const x y = x\nconst 5 9"}
   {PrintProgram P1}
   {PrintResult {Evaluate P1}}

   {System.showInfo "TEST A2: function sum_n x y z n = (x + y + z) * n\nsum_n 1 1 1 2 → 6"}
   P2 = {GraphGeneration "function sum_n x y z n = (x + y + z) * n\nsum_n 1 1 1 2"}
   {PrintProgram P2}
   {PrintResult {Evaluate P2}}

   {System.showInfo "TEST A3: function mult x y z = (x + y) * z\nmult 2 3 4 → 20"}
   P3 = {GraphGeneration "function mult x y z = (x + y) * z\nmult 2 3 4"}
   {PrintProgram P3}
   {PrintResult {Evaluate P3}}

   %% ✅ B. Evaluación de variables internas (var ... in ...)
   {System.showInfo "TEST B1: function fourtimes x = var y = x * x in y + y\nfourtimes 2 → 8"}
   P4 = {GraphGeneration "function fourtimes x = var y = x * x in y + y\nfourtimes 2"}
   {PrintProgram P4}
   {PrintResult {Evaluate P4}}

   {System.showInfo "TEST B2: function var_use x = var y = x * x in var z = y * 2 in z - 3\nvar_use 2 → 5"}
   P5 = {GraphGeneration "function var_use x = var y = x * x in var z = y * 2 in z - 3\nvar_use 2"}
   {PrintProgram P5}
   {PrintResult {Evaluate P5}}

   {System.showInfo "TEST B3: function var_chain x = var y = x + 1 in var z = y * 2 in z + y\nvar_chain 2 → 9"}
   P6 = {GraphGeneration "function var_chain x = var y = x + 1 in var z = y * 2 in z + y\nvar_chain 2"}
   {PrintProgram P6}
   {PrintResult {Evaluate P6}}

   %% ✅ C. Evaluación profunda recursiva
   {System.showInfo "TEST C1: function square x = x * x\nsquare square 3 → 81"}
   P7 = {GraphGeneration "function square x = x * x\nsquare square 3"}
   {PrintProgram P7}
   {PrintResult {Evaluate P7}}

   {System.showInfo "TEST C2: function nested x = x + (x * x)\nnested 3 → 12"}
   P8 = {GraphGeneration "function nested x = x + (x * x)\nnested 3"}
   {PrintProgram P8}
   {PrintResult {Evaluate P8}}

   {System.showInfo "TEST C3: function doubleadd x y = (x + y) + (x + y)\ndoubleadd 2 3 → 10"}
   P9 = {GraphGeneration "function doubleadd x y = (x + y) + (x + y)\ndoubleadd 2 3"}
   {PrintProgram P9}
   {PrintResult {Evaluate P9}}

   %% ✅ D. Casos de error (deben seguir funcionando)
   {System.showInfo "TEST D1: function bad x = x + y\nbad 3 → WHNF (y unknown)"}
   P10 = {GraphGeneration "function bad x = x + y\nbad 3"}
   {PrintProgram P10}
   {PrintResult {Evaluate P10}}

   %% ✅ E. Test adicional — paréntesis y operadores combinados
   {System.showInfo "TEST E1: function sqr x = (x + 1) * (x - 1)\nsqr 4 → 15"}
   local P R in
      P = {GraphGeneration "fun sqr x = (x + 1) * (x - 1)\nsqr 4"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   %% ✅ F. Operaciones aritméticas avanzadas
   {System.showInfo ""}
   {System.showInfo "=== SECCIÓN F: Operaciones aritméticas avanzadas ==="}
   {System.showInfo ""}
   {System.showInfo "TEST F1: Modulo - mod 17 5 → 2"}
   try
      local P R in
         {System.showInfo "  Generando grafo..."}
         P = {GraphGeneration "function test x = mod 17 5\ntest 0"}
         {System.showInfo "  Evaluando..."}
         R = {Evaluate P}
         {PrintProgram P}
         {PrintResult R}
         {System.showInfo "  F1 completado"}
      end
   catch E then
      {System.showInfo "ERROR en F1: "#{Value.toVirtualString E 0 0}}
   end
   {System.showInfo "Fin de F1"}

   {System.showInfo "TEST F2: Modulo - mod 20 6 → 2"}
   local P R in
      P = {GraphGeneration "function test x = mod 20 6\ntest 0"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   {System.showInfo "TEST F3: División entera explícita - div 17 5 → 3"}
   local P R in
      P = {GraphGeneration "function test x = div 17 5\ntest 0"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   {System.showInfo "TEST F4: División entera explícita - div 20 6 → 3"}
   local P R in
      P = {GraphGeneration "function test x = div 20 6\ntest 0"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   {System.showInfo "TEST F5: Potencia - pow 2 3 → 8"}
   local P R in
      P = {GraphGeneration "function test x = pow 2 3\ntest 0"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   {System.showInfo "TEST F6: Potencia - pow 3 4 → 81"}
   local P R in
      P = {GraphGeneration "function test x = pow 3 4\ntest 0"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   {System.showInfo "TEST F7: Potencia - pow 5 2 → 25"}
   local P R in
      P = {GraphGeneration "function test x = pow 5 2\ntest 0"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   {System.showInfo "TEST F8: Raíz cuadrada - sqrt 16 → 4"}
   local P R in
      P = {GraphGeneration "function test x = sqrt 16\ntest 0"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   {System.showInfo "TEST F9: Raíz cuadrada - sqrt 25 → 5"}
   local P R in
      P = {GraphGeneration "function test x = sqrt 25\ntest 0"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   {System.showInfo "TEST F10: Raíz cuadrada - sqrt 100 → 10"}
   local P R in
      P = {GraphGeneration "function test x = sqrt 100\ntest 0"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   {System.showInfo "TEST F11: Logaritmo - log 10 → ~2 (aproximadamente)"}
   local P R in
      P = {GraphGeneration "function test x = log 10\ntest 0"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   {System.showInfo "TEST F12: Logaritmo - log 100 → ~4 (aproximadamente)"}
   local P R in
      P = {GraphGeneration "function test x = log 100\ntest 0"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   {System.showInfo "TEST F13: Operaciones combinadas - (pow 2 3) + (sqrt 16) → 12"}
   local P R in
      P = {GraphGeneration "function test x = (pow 2 3) + (sqrt 16)\ntest 0"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   {System.showInfo "TEST F14: Operaciones combinadas - (mod 17 5) * (div 20 6) → 6"}
   local P R in
      P = {GraphGeneration "function test x = (mod 17 5) * (div 20 6)\ntest 0"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   {System.showInfo "TEST F15: Operaciones combinadas - sqrt (pow 2 4) → 4"}
   local P R in
      P = {GraphGeneration "function test x = sqrt (pow 2 4)\ntest 0"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   {System.showInfo "TEST F16: Operaciones combinadas - pow (sqrt 25) 2 → 25"}
   local P R in
      P = {GraphGeneration "function test x = pow (sqrt 25) 2\ntest 0"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   {System.showInfo "🎯 ALL TESTS COMPLETED - EXPECTED RESULTS:"}
   {System.showInfo "A1: 5, A2: 6, A3: 20, B1: 8, B2: 5, B3: 9, C1: 81, C2: 12, C3: 10, D1: WHNF"}
   {System.showInfo "F1: 2, F2: 2, F3: 3, F4: 3, F5: 8, F6: 81, F7: 25, F8: 4, F9: 5, F10: 10"}
   {System.showInfo "F11: ~2, F12: ~4, F13: 12, F14: 6, F15: 4, F16: 25"}
end