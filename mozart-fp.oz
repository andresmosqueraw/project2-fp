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
   {Map {String.tokens S & } fun {$ L} {String.toAtom L} end}
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
   [] [X] then {Leaf X}
   [] X|Y|nil then {App {Leaf X} {Leaf Y}}
   [] X|Rest then {App {Leaf X} {BuildExpr Rest}}
   end
end

%% ────────────────────────────────────────────────
%% STEP 3 – Full program graph generator
%% ────────────────────────────────────────────────

fun {GraphGeneration ProgramStr}
   local
      Lines TokensDef TokensCall FName ArgName BodyTokens FunBody CallGraph
   in
      %% Split lines
      Lines = {String.tokens ProgramStr &\n}

      if {Length Lines} < 2 then
         raise error('Program must have two lines: definition and call') end
      end

      %% Tokenize each line
      TokensDef  = {CleanTokens {Str2Lst {List.nth Lines 1}}}
      TokensCall = {CleanTokens {Str2Lst {List.nth Lines 2}}}

      %% Expect form: function <name> <arg> = <body...>
      if {List.nth TokensDef 1} \= function then
         raise error('Definition must start with function') end
      end

      FName    = {List.nth TokensDef 2}
      ArgName  = {List.nth TokensDef 3}
      BodyTokens = {List.drop TokensDef 4}   %% after function name arg =

      %% Build graphs
      FunBody   = {BuildExpr BodyTokens}
      CallGraph = {BuildExpr TokensCall}

      %% Return structure
      prog(function:FName arg:ArgName body:FunBody call:CallGraph)
   end
end

%% ────────────────────────────────────────────────
%% STEP 4 – Tests
%% ────────────────────────────────────────────────

local G1 G2 in
   G1 = {GraphGeneration "function square x = x * x\nsquare square 3"}
   {Show G1}

   G2 = {GraphGeneration "function twice x = x + x\ntwice 5"}
   {Show G2}
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
 %%  Entrada: prog(function: FName arg: ... body: ... call: CallGraph)
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
    %% square square 3
    P1 = {GraphGeneration "function square x = x * x\nsquare square 3"}
    R1 = {NextReduction P1}
    {Show P1}
    {Show R1}
 
    %% twice 5
    P2 = {GraphGeneration "function twice x = x + x\ntwice 5"}
    R2 = {NextReduction P2}
    {Show P2}
    {Show R2}
 
    %% + 2 (falta arg) → WHNF sobre primitiva
    P3 = prog(function:'f' arg:x
              body:leaf(var:x)
              call:app(function:leaf(var:'+') arg:leaf(num:2)))
    R3 = {NextReduction P3}
    {Show P3}
    {Show R3}
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

%% Evalúa una subexpresión hasta número usando una pequeña “máquina”
%%   (vuelve a usar NextReduction + Reduce sobre un programa temporal)
fun {EvalToNum Expr Prog}
   case Expr
   of leaf(num:N) then N
   else
      local P R P2 in
         P  = prog(function:Prog.function arg:Prog.arg body:Prog.body call:Expr)
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
            %% Instanciar cuerpo con el/los argumentos consumidos
            %% (nuestro mini-lenguaje tiene 1 parámetro)
            local ArgNode Instanced in
               ArgNode  = {List.nth R.args 1}
               Instanced = {Subst Prog.body Prog.arg ArgNode}
               %% si hay más argumentos en la aplicación externa, reaplícalos
               NewNode  = {ApplyRest Instanced R.rest}
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
         prog(function:Prog.function arg:Prog.arg body:Prog.body call:NewCall)
      end
   end
end

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 🔬 Tests Task 3
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

local P1 S1 P2 S2 P3 S3 in
   %% 1) (square square) 3 → ( (square 3) * (square 3) )
   P1 = {GraphGeneration "function square x = x * x\nsquare square 3"}
   S1 = {Reduce P1}
   {Show P1}
   {Show S1}

   %% 2) (twice 5) → (5 + 5) y una segunda reducción (primitiva)
   P2 = {GraphGeneration "function twice x = x + x\ntwice 5"}
   S2 = {Reduce P2}
   {Show P2}
   {Show S2}
   %% Un paso más para verificar primitivas
   {Show {Reduce S2}}

   %% 3) (+ 2 3) → 5
   P3 = prog(function:'f' arg:x body:leaf(var:x)
             call:app(function:app(function:leaf(var:'+') arg:leaf(num:2))
                           arg:leaf(num:3)))
   S3 = {Reduce P3}
   {Show P3}
   {Show S3}
end
