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

%% ==========================================================
%% ✅ CORRECCIÓN: aplicaciones asociativas a la izquierda
%% ==========================================================
fun {BuildLeft F Ts}
   case Ts
   of nil then F
   [] T|Tr then {BuildLeft app(function:F arg:{Leaf T}) Tr}
   end
end

%% ---------- Infix parsing helpers (shunting-yard) ----------
%% ---------- Infix parsing helpers (shunting-yard) ----------
fun {IsOp T}
   %% Solo operadores infijos verdaderos
   {List.member T ['+' '-' '*' '/']}
end

fun {Prec Op}
   case Op
   of '+' then 1
   [] '-' then 1
   [] '*' then 2
   [] '/' then 2
   else 0
   end
end

fun {AssocLeft Op} true end  %% todos left-assoc aquí

%% Convierte lista de tokens infijos a RPN (lista)
fun {ToRPN Tokens}
   fun {Loop Ts Out Stk}
      case Ts
      of nil then {Append Out {Reverse Stk}}
      [] '('|Tr then {Loop Tr Out '('|Stk}
      [] ')'|Tr then
         local Popped Rest PopUntilOpen in
            %% pop hasta '('
            fun {PopUntilOpen S Acc}
               case S
               of nil then raise error('mismatched_parens') end
               [] '('|Sr then Acc#Sr
               [] Op|Sr then {PopUntilOpen Sr Op|Acc}
               end
            end
            Popped#Rest = {PopUntilOpen Stk nil}
            {Loop Tr {Append Out {Reverse Popped}} Rest}
         end
      [] T|Tr then
         if {IsOp T} then
            %% pop operadores de mayor/igual precedencia
            local S2 Out2 PopOps in
               fun {PopOps S O Acc}
                  case S
                  of nil then Acc#nil
                  [] Op2|Sr then
                     if {IsOp Op2} andthen
                        (({AssocLeft O} andthen {Prec O} =< {Prec Op2})
                         orelse ({Prec O} < {Prec Op2}))
                     then
                        {PopOps Sr O Op2|Acc}
                     else
                        Acc#S
                     end
                  end
               end
               Out2#S2 = {PopOps Stk T nil}
               {Loop Tr {Append Out {Reverse Out2}} T|S2}
            end
         else
            %% operando (número, var, 'rad' como función prefija, etc.)
            {Loop Tr {Append Out [T]} Stk}
         end
      end
   end
in
   {Loop Tokens nil nil}
end

%% De RPN a tu AST usando curriado: (+ a b) = app(app(+) a) b
fun {RPNtoAST RPN}
   fun {Push S X} X|S end
   fun {Pop2 S}
      %% A (top) = right, B = left
      case S
      of A|B|Sr then A#B#Sr
      [] _ then raise error('rpn_stack_underflow') end
      end
   end
   fun {Loop L Stk}
      case L
      of nil then
         case Stk
         of [X] then X
         [] _ then raise error('rpn_final_stack') end
         end
      [] Tok|Tr then
         if {IsOp Tok} then
            local A B Rest in
               A#B#Rest = {Pop2 Stk}          %% A=right, B=left
               %% app(app(op) left) right
               {Loop Tr {Push Rest app(function:app(function:leaf(var:Tok) arg:B) arg:A)}}
            end
         else
            {Loop Tr {Push Stk {Leaf Tok}}}
         end
      end
   end
in
   {Loop RPN nil}
end

%% Detecta si conviene ruta infija (contiene op o paréntesis)
fun {LooksInfix Ts}
   {List.member '(' Ts} orelse {List.member ')' Ts} orelse
   ({List.filter Ts IsOp} \= nil)
end

fun {BuildExpr Tokens}
   case Tokens
   of nil then unit

   %% var ... in ...
   [] 'var'|VarName|'='|Rest then
      local BindTokens BodyTokens in
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

   %% un solo token → hoja
   [] [X] then {Leaf X}

   %% >>> NUEVO: si parece infijo, parsear con precedencia <<<
   [] Xs then
      if {LooksInfix Xs} then
         {RPNtoAST {ToRPN Xs}}
      else
         %% 2+ tokens prefijo → aplicación izquierda ((f a1) a2)
         case Xs of H|Rest then {BuildLeft {Leaf H} Rest} end
      end
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

      %% expect "fun <name> <arg1> <arg2> ... = <body>" or "fun <name> ..."
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
   G2 = {GraphGeneration "fun twice x = x + x\ntwice 5"}
   {PrintProgram G2}
end


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 📘 FP Project – Task 2: NextReduction
%%  - Encuentra la redex externa (outermost) para reducir
%%  - Si faltan argumentos → WHNF
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% ¿Es operador primitivo?
fun {IsPrimitive Op}
   {List.member Op ['+' '-' '*' '/' 'rad']}
end

%% ¿Es operador unario?
fun {IsUnary Op}
   false
end

%% ¿Es operador binario?
fun {IsBinary Op}
   {List.member Op ['+' '-' '*' '/' 'rad']}
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

fun {MakeApp F Args}
   case Args
   of nil then F
   [] A|Ar then {MakeApp app(function:F arg:A) Ar}
   end
end
 
%% NextReduction:
%%  Entrada: prog(function: FName args: ... body: ... call: CallGraph)
 %%  Salida:  record con la info de la redex externa
 %%           redex(kind:primitive/supercombinator/..., head:Head,
 %%                 arity:K, args:ArgsK, rest:RemainingArgs,
 %%                 root:RootAppNode, apps:SpineApps, allargs:AllArgs,
 %%                 status:ok|whnf|stuck)
 fun {NextReduction Prog}
   local UW Head K Apps AllArgs ArgsK Remaining Kind Root in
      UW      = {Unwind Prog.call nil nil}
      Head    = UW.head
      AllArgs = UW.args
      Apps    = UW.apps
      K       = {HeadArity Head Prog}
      Kind    = {HeadKind Head Prog}

      if K==0 then
         redex(status:stuck kind:Kind head:Head allargs:AllArgs apps:Apps)
      elseif {Length AllArgs} < K then
         redex(status:whnf kind:Kind head:Head arity:K allargs:AllArgs apps:Apps)
      else
         ArgsK     = {List.take AllArgs K}
         Remaining = {List.drop AllArgs K}
         Root      = {MakeApp Head ArgsK}   %% 👈 reconstrucción directa
         redex(status:ok kind:Kind head:Head arity:K
               args:ArgsK rest:Remaining
               root:Root apps:Apps allargs:AllArgs)
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
   P1 = {GraphGeneration "fun square x = x * x\nsquare square 3"}
   R1 = {NextReduction P1}
   {PrintProgram P1}
   {PrintRedex R1}

   %% twice 5
   {System.showInfo "TEST 2: twice 5"}
   P2 = {GraphGeneration "fun twice x = x + x\ntwice 5"}
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
%% ==========================================
%% 🔧 EvalToNum — evita bucles con radicación
%% ==========================================
%% ==========================================
%% ✅ EvalToNum — versión sin atajos de primitivas
%%    (evita loops en aplicaciones curried como rad)
%% ==========================================
fun {EvalToNum Expr Prog}
   case Expr
   of leaf(num:N) then N
   [] leaf(var:_) then
      raise error('expected_number'(expr:Expr status:whnf)) end
   [] var(bindings:Bs body:B) then
      %% evalúa primero los 'var ... in ...'
      local EvaluatedBody in
         EvaluatedBody = {EvalVarBindings Bs B}
         {EvalToNum EvaluatedBody Prog}
      end
   [] app(function:_ arg:_) then
      %% Delega SIEMPRE en la máquina de reducción, con guardia
      local P R P2 in
         P  = prog(function:Prog.function args:Prog.args body:Prog.body call:Expr)
         R  = {NextReduction P}
         if R.status == ok then
            P2 = {Reduce P}
            %% Guardia: si no hubo progreso, corta (evita ciclo)
            if {Value.equal P2.call P.call} then
               raise error('stuck_in_evaltonum'(expr:Expr)) end
            else
               {EvalToNum P2.call P2}
            end
         elseif R.status == whnf then
            raise error('expected_number'(expr:Expr status:R.status)) end
         else
            raise error('expected_number'(expr:Expr status:R.status)) end
         end
      end
   else
      %% Cualquier otro nodo que no sea número / var / app
      raise error('unexpected_expr_in_evaltonum'(expr:Expr)) end
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
            %% Evaluar ambos argumentos a número y calcular
            local A1 A2 N1 N2 Res in
               A1 = {List.nth R.args 1}
               A2 = {List.nth R.args 2}
               try
                  N1 = {EvalToNum A1 Prog}
                  N2 = {EvalToNum A2 Prog}
                  if Op=='rad' then
                     if N2 == 0 then
                        raise error('zero_root_not_allowed'(base:N1)) end
                     else
                        %% cálculo estable: usa floats pero devuelve int
                        local Rv in
                           Rv = {Float.pow {Int.toFloat N1} (1.0/{Int.toFloat N2})}
                           if Rv \= Rv orelse Rv == ~1.0/0.0 then
                              raise error('invalid_rad_result'(base:N1 index:N2)) end
                           else
                              Res = {Float.toInt Rv}
                           end
                        end
                     end
                  else
                     Res =
                        case Op
                        of '+' then N1+N2
                        [] '-' then N1-N2
                        [] '*' then N1*N2
                        [] '/' then N1 div N2
                        else
                           raise error('unknown_operator'(op:Op)) end
                        end
                  end
                  NewNode = {ApplyRest leaf(num:Res) R.rest}
               catch _ then
                  %% Aún no se pueden evaluar los argumentos: no cambiar
                  NewNode = R.root
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
   P1 = {GraphGeneration "fun square x = x * x\nsquare square 3"}
   S1 = {Reduce P1}
   {PrintProgram P1}
   {System.showInfo "After one reduction:"}
   {PrintProgram S1}

   %% 2) (twice 5) → (5 + 5) y una segunda reducción (primitiva)
   {System.showInfo "TEST 2: (twice 5) → (5 + 5) → 10"}
   P2 = {GraphGeneration "fun twice x = x + x\ntwice 5"}
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
      R = {NextReduction Prog}
      if R.status == ok then
         %% hay redex → reduce y continúa
         Pnext = {Reduce Prog}
         if Pnext.call==Prog.call then
            %% sin progreso: devuelve el programa tal cual (o lanza error si prefieres)
            Prog
         else
            {Evaluate Pnext}
         end         
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
         [] app(function:F arg:A) then
            %% Evaluar recursivamente función y argumento
            local EvalF EvalA in
               EvalF = {EvaluateDeep F Prog}
               EvalA = {EvaluateDeep A Prog}
               case EvalF#EvalA
               of leaf(num:NF)#leaf(num:NA) then
                  %% Aplicar operación si es primitiva
                  case F
                  of leaf(var:Op) then
                     case Op
                     of '+' then NF + NA
                     [] '-' then NF - NA
                     [] '*' then NF * NA
                     [] '/' then NF div NA
                     [] 'rad' then
                         if NA == 0 then
                            raise error('zero_root_not_allowed'(base:NF)) end
                         else
                            {Float.toInt {Float.pow {Int.toFloat NF} (1.0/{Int.toFloat NA})}}
                         end                     
                     else
                        %% No es primitiva, crear nueva aplicación
                        local NewProg in
                           NewProg = prog(function:Prog.function args:Prog.args body:Prog.body 
                                         call:app(function:EvalF arg:EvalA))
                           {Evaluate NewProg}
                        end
                     end
                  else
                     %% No es primitiva, crear nueva aplicación
                     local NewProg in
                        NewProg = prog(function:Prog.function args:Prog.args body:Prog.body 
                                      call:app(function:EvalF arg:EvalA))
                        {Evaluate NewProg}
                     end
                  end
               [] _#_ then
                  %% Al menos uno no es número, crear nueva aplicación
                  local NewProg in
                     NewProg = prog(function:Prog.function args:Prog.args body:Prog.body 
                                   call:app(function:EvalF arg:EvalA))
                     {Evaluate NewProg}
                  end
               end
            end
         [] _ then
            %% No es var ni app, devolver el grafo
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
   P1 = {GraphGeneration "fun square x = x * x\nsquare square 3"}
   R1 = {Evaluate P1}
   {PrintProgram P1}
   {PrintResult R1}

   %% Ejemplo 2 — fourtimes 2 → 8
   %% (extiende lenguaje: var y = x*x in y+y)
   %% Se comportará igual que (x*x)+(x*x)
   {System.showInfo "TEST 2: fourtimes 2 → 8"}
   P2 = {GraphGeneration "fun fourtimes x = x * x + x * x\nfourtimes 2"}
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
   P1 = {GraphGeneration "fun sum_n x y z n = (x + y + z) * n\nsum_n 1 1 1 2"}
   {PrintProgram P1}
   {PrintResult {Evaluate P1}}

   %% Variable interna
   {System.showInfo "TEST 2: Internal variables - var_use 2 → 5"}
   P2 = {GraphGeneration "fun var_use x = var y = x * x in var z = y * 2 in z - 3\nvar_use 2"}
   {PrintProgram P2}
   {PrintResult {Evaluate P2}}

   %% Nesting complejo
   {System.showInfo "TEST 3: Complex nesting - arithmetic with nested calls"}
   P3 = {GraphGeneration "fun arithmetic x y = ((x + y) / (x - y)) * 2\narithmetic arithmetic 5 6 arithmetic 2 11"}
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
   {System.showInfo "TEST A1: fun const x y = x\nconst 5 9 → 5"}
   P1 = {GraphGeneration "fun const x y = x\nconst 5 9"}
   {PrintProgram P1}
   {PrintResult {Evaluate P1}}

   {System.showInfo "TEST A2: fun sum_n x y z n = (x + y + z) * n\nsum_n 1 1 1 2 → 6"}
   P2 = {GraphGeneration "fun sum_n x y z n = (x + y + z) * n\nsum_n 1 1 1 2"}
   {PrintProgram P2}
   {PrintResult {Evaluate P2}}

   {System.showInfo "TEST A3: fun mult x y z = (x + y) * z\nmult 2 3 4 → 20"}
   P3 = {GraphGeneration "fun mult x y z = (x + y) * z\nmult 2 3 4"}
   {PrintProgram P3}
   {PrintResult {Evaluate P3}}

   %% ✅ B. Evaluación de variables internas (var ... in ...)
   {System.showInfo "TEST B1: fun fourtimes x = var y = x * x in y + y\nfourtimes 2 → 8"}
   P4 = {GraphGeneration "fun fourtimes x = var y = x * x in y + y\nfourtimes 2"}
   {PrintProgram P4}
   {PrintResult {Evaluate P4}}

   {System.showInfo "TEST B2: fun var_use x = var y = x * x in var z = y * 2 in z - 3\nvar_use 2 → 5"}
   P5 = {GraphGeneration "fun var_use x = var y = x * x in var z = y * 2 in z - 3\nvar_use 2"}
   {PrintProgram P5}
   {PrintResult {Evaluate P5}}

   {System.showInfo "TEST B3: fun var_chain x = var y = x + 1 in var z = y * 2 in z + y\nvar_chain 2 → 9"}
   P6 = {GraphGeneration "fun var_chain x = var y = x + 1 in var z = y * 2 in z + y\nvar_chain 2"}
   {PrintProgram P6}
   {PrintResult {Evaluate P6}}

   %% ✅ C. Evaluación profunda recursiva
   {System.showInfo "TEST C1: fun square x = x * x\nsquare square 3 → 81"}
   P7 = {GraphGeneration "fun square x = x * x\nsquare square 3"}
   {PrintProgram P7}
   {PrintResult {Evaluate P7}}

   {System.showInfo "TEST C2: fun nested x = x + (x * x)\nnested 3 → 12"}
   P8 = {GraphGeneration "fun nested x = x + (x * x)\nnested 3"}
   {PrintProgram P8}
   {PrintResult {Evaluate P8}}

   {System.showInfo "TEST C3: fun doubleadd x y = (x + y) + (x + y)\ndoubleadd 2 3 → 10"}
   P9 = {GraphGeneration "fun doubleadd x y = (x + y) + (x + y)\ndoubleadd 2 3"}
   {PrintProgram P9}
   {PrintResult {Evaluate P9}}

   %% ✅ D. Casos de error (deben seguir funcionando)
   {System.showInfo "TEST D1: fun bad x = x + y\nbad 3 → WHNF (y unknown)"}
   P10 = {GraphGeneration "fun bad x = x + y\nbad 3"}
   {PrintProgram P10}
   {PrintResult {Evaluate P10}}

   %% ✅ E. Test adicional — paréntesis y operadores combinados
   {System.showInfo "TEST E1: fun sqr x = (x + 1) * (x - 1)\nsqr 4 → 15"}
   local P R in
      P = {GraphGeneration "fun sqr x = (x + 1) * (x - 1)\nsqr 4"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   {System.showInfo "🎯 ALL TESTS COMPLETED - EXPECTED RESULTS:"}
   {System.showInfo "A1: 5, A2: 6, A3: 20, B1: 8, B2: 5, B3: 9, C1: 81, C2: 12, C3: 10, D1: WHNF"}

   %% ✅ F.17–20 Radicación (raíces n-ésimas)
   {System.showInfo ""}
   {System.showInfo "=== SECCIÓN F (continuación): Radicación ==="}
   {System.showInfo ""}

   {System.showInfo "TEST F17: Raíz cuadrada (rad 9 2) → 3"}
   local P R in
      P = {GraphGeneration "fun test x = rad 9 2\ntest 0"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   {System.showInfo "TEST F18: Raíz cúbica (rad 27 3) → 3"}
   local P R in
      P = {GraphGeneration "fun test x = rad 27 3\ntest 0"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   {System.showInfo "TEST F19: Raíz cuarta (rad 16 4) → 2"}
   local P R in
      P = {GraphGeneration "fun test x = rad 16 4\ntest 0"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   {System.showInfo "TEST F16b: Raíz cuadrada repetida (rad (rad 256 2) 2) → 4"}
   local P R in
      P = {GraphGeneration "fun test x = rad (rad 256 2) 2\ntest 0"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   {System.showInfo "TEST F20: Radicación combinada (rad (rad 81 4) 2) → 3"}
   local P R in
      P = {GraphGeneration "fun test x = rad (rad 81 4) 2\ntest 0"}
      R = {Evaluate P}
      {PrintProgram P}
      {PrintResult R}
   end

   {System.showInfo "🎯 NUEVOS TESTS DE RADICACIÓN COMPLETADOS"}
   {System.showInfo "F17: 3, F18: 3, F19: 2, F20: 3"}
end