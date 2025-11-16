%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Task 1
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

declare

%% ────────────────────────────────────────────────
%% Utilities
%% ────────────────────────────────────────────────

fun {Str2Lst S}
   local
      fun {InsDelims Cs}
         case Cs
         of nil then nil
         [] C|Cr then
            if C==&( orelse C==&) orelse C==&, then
               & | C | & | {InsDelims Cr}
            else
               C | {InsDelims Cr}
            end
         end
      end
      Cleaned = {InsDelims {VirtualString.toString S}}
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
%% STEP 1
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
%% STEP 2
%% ────────────────────────────────────────────────
fun {BuildRight Ts}
   case Ts
   of [X] then {Leaf X}
   [] H|Tr then app(function:{Leaf H} arg:{BuildRight Tr})
   end
end

fun {IsOp T}
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

fun {AssocLeft Op} true end

fun {ToRPN Tokens}
   {System.showInfo "=== DEBUG ToRPN ==="}
   {System.showInfo "Input tokens: "#{Value.toVirtualString Tokens 0 0}}
   fun {Loop Ts Out Stk}
      case Ts
      of nil then
         local Result in
            Result = {Append Out Stk}
            {System.showInfo "Final RPN: "#{Value.toVirtualString Result 0 0}}
            Result
         end
      [] '('|Tr then {Loop Tr Out '('|Stk}
      [] ')'|Tr then
         local Popped Rest PopUntilOpen in
            fun {PopUntilOpen S Acc}
               case S
               of nil then raise error('mismatched_parens') end
               [] '('|Sr then Acc#Sr
               [] Op|Sr then {PopUntilOpen Sr Op|Acc}
               end
            end
            Popped#Rest = {PopUntilOpen Stk nil}
            {Loop Tr {Append Out Popped} Rest}
         end
      [] T|Tr then
         if {IsOp T} then
            local S2 Out2 PopOps in
               fun {PopOps S O Acc}
                  case S
                  of nil then Acc#nil
                  [] '('|_ then Acc#S
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
               {System.showInfo "  Operator: "#{Value.toVirtualString T 0 0}#" | Out: "#{Value.toVirtualString Out2 0 0}#" | Stack: "#{Value.toVirtualString S2 0 0}}
               {Loop Tr {Append Out Out2} T|S2}
            end
         else
            {System.showInfo "  Token: "#{Value.toVirtualString T 0 0}}
            {Loop Tr {Append Out [T]} Stk}
         end
      end
   end
in
   {Loop Tokens nil nil}
end

fun {RPNtoAST RPN}
   {System.showInfo "=== DEBUG RPNtoAST ==="}
   {System.showInfo "Input RPN: "#{Value.toVirtualString RPN 0 0}}
   fun {Push S X} X|S end
   fun {Pop2 S}
      case S
      of A|B|Sr then A#B#Sr
      [] _ then raise error('rpn_stack_underflow') end
      end
   end
   fun {Loop L Stk}
      case L
      of nil then
         case Stk
         of [X] then
            {System.showInfo "Final AST: "#{Value.toVirtualString X 0 0}}
            X
         [] _ then raise error('rpn_final_stack') end
         end
      [] Tok|Tr then
         if {IsOp Tok} then
            local A B Rest NewNode in
               A#B#Rest = {Pop2 Stk}
               {System.showInfo "  Operator: "#{Value.toVirtualString Tok 0 0}#" | A: "#{Value.toVirtualString A 0 0}#" | B: "#{Value.toVirtualString B 0 0}}
               NewNode = app(function:app(function:leaf(var:Tok) arg:B) arg:A)
               {System.showInfo "  Created node: "#{Value.toVirtualString NewNode 0 0}}
               {Loop Tr {Push Rest NewNode}}
            end
         else
            local LeafNode in
               LeafNode = {Leaf Tok}
               {System.showInfo "  Token: "#{Value.toVirtualString Tok 0 0}#" -> Leaf: "#{Value.toVirtualString LeafNode 0 0}}
               {Loop Tr {Push Stk LeafNode}}
            end
         end
      end
   end
in
   {Loop RPN nil}
end

fun {LooksInfix Ts}
   ({List.filter Ts IsOp} \= nil)
end

fun {BuildLeftFrom F Ts}
   case Ts
   of nil then F
   [] H|T then {BuildLeftFrom app(function:F arg:{Leaf H}) T}
   end
end

fun {BuildLeft Ts}
   case Ts
   of [X] then {Leaf X}
   [] H|T then {BuildLeftFrom {Leaf H} T}
   end
end

fun {BuildExpr Tokens}
   {System.showInfo "=== DEBUG BuildExpr ==="}
   {System.showInfo "Input tokens: "#{Value.toVirtualString Tokens 0 0}}
   case Tokens
   of nil then unit
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

   [] [X] then {Leaf X}

   [] Xs then
      if {LooksInfix Xs} then
         {System.showInfo "  Detected infix expression"}
         {RPNtoAST {ToRPN Xs}}
      else
         {System.showInfo "  Not infix, using BuildLeft/BuildRight"}
         local Y in
            Y = {List.filter Xs fun {$ T} T \= '(' andthen T \= ')' end}
            if Y \= nil andthen {IsOp {List.nth Y 1}} then
               {BuildLeft Y}
            else
               {BuildLeft Y}
            end
         end
      end   
   end
end

%% ────────────────────────────────────────────────
%% STEP 3
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

      local FirstToken in
         FirstToken = {List.nth TokensDef 1}
         if FirstToken \= 'fun' andthen FirstToken \= function then
            raise error('Definition must start with fun or function') end
         end
      end

      FName = {List.nth TokensDef 2}

      local EqPos in
         EqPos = {FindIndex TokensDef fun {$ X} X=='=' end}
         if EqPos == false then
            raise error('Missing "=" in definition') end
         end
         ArgsTokens = {List.drop {List.take TokensDef (EqPos-1)} 2}
         BodyTokens = {List.drop TokensDef EqPos}
      end

      {System.showInfo "=== DEBUG GraphGeneration START ==="}
      {System.showInfo "ProgramStr: "#ProgramStr}
      {System.showInfo "BodyTokens: "#{Value.toVirtualString BodyTokens 0 0}}
      {System.showInfo "TokensCall: "#{Value.toVirtualString TokensCall 0 0}}

      FunBody   = {BuildExpr BodyTokens}
      {System.showInfo "After BuildExpr BodyTokens - FunBody created"}
      {System.showInfo "FunBody value: "#{Value.toVirtualString FunBody 0 0}}
      
      CallGraph = {BuildExpr TokensCall}
      {System.showInfo "After BuildExpr TokensCall - CallGraph created"}
      {System.showInfo "CallGraph value: "#{Value.toVirtualString CallGraph 0 0}}

      {System.showInfo "=== DEBUG GraphGeneration BEFORE prog creation ==="}
      {System.showInfo "Function: "#{Value.toVirtualString FName 0 0}}
      {System.showInfo "Args: "#{Value.toVirtualString ArgsTokens 0 0}}
      {System.showInfo "Body AST: "#{Value.toVirtualString FunBody 0 0}}
      {System.showInfo "Call AST: "#{Value.toVirtualString CallGraph 0 0}}
      
      {System.showInfo "Creating prog record..."}
      local ProgResult in
         ProgResult = prog(function:FName args:ArgsTokens body:FunBody call:CallGraph)
         {System.showInfo "prog record created successfully"}
         {System.showInfo "ProgResult: "#{Value.toVirtualString ProgResult 0 0}}
         ProgResult
      end
   end
end

%% ────────────────────────────────────────────────
%% STEP 4
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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Task 2
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fun {IsPrimitive Op}
   {List.member Op ['+' '-' '*' '/' 'rad']}
end

fun {IsUnary Op}
   false
end

fun {IsBinary Op}
   {List.member Op ['+' '-' '*' '/' 'rad']}
end

 
 fun {HeadArity Head Prog}
    {System.showInfo "=== DEBUG HeadArity ==="}
    {System.showInfo "Head: "#{Value.toVirtualString Head 0 0}#", Prog.function: "#{Value.toVirtualString Prog.function 0 0}#""}
    local Result in
       case Head
       of leaf(var:Op) then
          if {IsPrimitive Op} then
             {System.showInfo ">>> Head is primitive, returning arity 2"}
             Result = 2
          elseif Op==Prog.function then
             {System.showInfo ">>> Head is supercombinator, returning arity: "#{Length Prog.args}}
             Result = {Length Prog.args}
          else
             {System.showInfo ">>> Head is variable, returning arity 0"}
             Result = 0
          end
       [] leaf(num:_) then
          {System.showInfo ">>> Head is number, returning arity 0"}
          Result = 0
       else
          {System.showInfo ">>> Head is other type, returning arity 0"}
          Result = 0
       end
       {System.showInfo ">>> HeadArity result: "#Result}
       Result
    end
 end
 
 fun {HeadKind Head Prog}
    {System.showInfo "=== DEBUG HeadKind ==="}
    {System.showInfo "Head: "#{Value.toVirtualString Head 0 0}#", Prog.function: "#{Value.toVirtualString Prog.function 0 0}#""}
    local Result in
       case Head
       of leaf(var:Op) then
          if {IsPrimitive Op} then
             {System.showInfo ">>> Head is primitive: "#{Value.toVirtualString Op 0 0}}
             Result = primitive(Op)
          elseif Op==Prog.function then
             {System.showInfo ">>> Head is supercombinator: "#{Value.toVirtualString Op 0 0}}
             Result = supercombinator(Op)
          else
             {System.showInfo ">>> Head is variable: "#{Value.toVirtualString Op 0 0}}
             Result = variable(Op)
          end
       [] leaf(num:N) then
          {System.showInfo ">>> Head is number: "#N}
          Result = number(N)
       else
          {System.showInfo ">>> Head is other type"}
          Result = other
       end
       {System.showInfo ">>> HeadKind result: "#{Value.toVirtualString Result 0 0}}
       Result
    end
 end
 
 fun {Unwind Expr Args Apps}
    {System.showInfo "=== DEBUG Unwind ==="}
    {System.showInfo "Expr: "#{Value.toVirtualString Expr 0 0}#", Args length: "#{Length Args}#", Apps length: "#{Length Apps}#""}
    case Expr
    of app(function:F arg:A) then
       {System.showInfo ">>> Unwind: Expr is app, unwinding further"}
       {Unwind F A|Args Expr|Apps}
    else
       {System.showInfo ">>> Unwind: Expr is not app, returning unwind(head: "#{Value.toVirtualString Expr 0 0}#", args length: "#{Length Args}#", apps length: "#{Length Apps}#")"}
       unwind(head:Expr args:Args apps:Apps)
    end
 end
 
 fun {Nth L I}
    {List.nth L I}
 end

fun {MakeApp F Args}
   case Args
   of nil then F
   [] A|Ar then {MakeApp app(function:F arg:A) Ar}
   end
end
 

 fun {NextReduction Prog}
   {System.showInfo "=== DEBUG NextReduction ==="}
   {System.showInfo "Prog.call: "#{Value.toVirtualString Prog.call 0 0}}
   local UW Head K Apps AllArgs ArgsK Remaining Kind Root in
      UW      = {Unwind Prog.call nil nil}
      Head    = UW.head
      AllArgs = UW.args
      Apps    = UW.apps
      {System.showInfo ">>> Unwound - Head: "#{Value.toVirtualString Head 0 0}#", AllArgs length: "#{Length AllArgs}}
      K       = {HeadArity Head Prog}
      Kind    = {HeadKind Head Prog}
      {System.showInfo ">>> HeadArity: "#K#", HeadKind: "#{Value.toVirtualString Kind 0 0}}

      if K==0 then
         {System.showInfo ">>> K==0, returning stuck"}
         redex(status:stuck kind:Kind head:Head allargs:AllArgs apps:Apps)
      elseif {Length AllArgs} < K then
         {System.showInfo ">>> AllArgs length ("#{Length AllArgs}#") < K ("#K#"), returning whnf"}
         redex(status:whnf kind:Kind head:Head arity:K allargs:AllArgs apps:Apps)
      else
         {System.showInfo ">>> AllArgs length ("#{Length AllArgs}#") >= K ("#K#"), returning ok"}
         ArgsK     = {List.take AllArgs K}
         Remaining = {List.drop AllArgs K}
         Root      = {MakeApp Head ArgsK}
         {System.showInfo ">>> ArgsK: "#{Value.toVirtualString ArgsK 0 0}#", Remaining length: "#{Length Remaining}}
         redex(status:ok kind:Kind head:Head arity:K
               args:ArgsK rest:Remaining
               root:Root apps:Apps allargs:AllArgs)
      end
   end
end
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Task 3
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
      var(bindings:{Map Bs fun {$ B}
                        bind(var:B.var expr:{Subst B.expr Var WithNode})
                     end}
          body:{Subst B Var WithNode})
   else
      Expr
   end
end

fun {ApplyRest Node Rest}
   case Rest
   of nil        then Node
   [] R|Rs then {ApplyRest app(function:Node arg:R) Rs}
   end
end

fun {EvalVarBindings Bindings Body Prog}
   {System.showInfo "=== DEBUG EvalVarBindings ==="}
   {System.showInfo "Bindings: "#{Value.toVirtualString Bindings 0 0}}
   {System.showInfo "Body: "#{Value.toVirtualString Body 0 0}}
   case Bindings
   of nil then
      {System.showInfo ">>> EvalVarBindings: All bindings processed, evaluating final body"}
      local FinalBodyProg FinalResult in
         FinalBodyProg = prog(function:Prog.function args:Prog.args body:Prog.body call:Body)
         {System.showInfo ">>> FinalBodyProg.call: "#{Value.toVirtualString Body 0 0}}
         FinalResult = {Evaluate FinalBodyProg}
         {System.showInfo ">>> FinalResult from Evaluate: "#{Value.toVirtualString FinalResult 0 0}}
         case FinalResult
         of leaf(num:N) then
            {System.showInfo ">>> EvalVarBindings returning integer from leaf(num): "#N}
            N
         [] N andthen {IsInt N} then
            {System.showInfo ">>> EvalVarBindings returning integer: "#N}
            N
         [] leaf(var:VarName) then
            {System.showInfo ">>> EvalVarBindings returning variable: "#{Value.toVirtualString FinalResult 0 0}}
            FinalResult
         [] app(function:_ arg:_) then
            {System.showInfo ">>> FinalResult is app, calling EvaluateDeep"}
            local EvaluatedDeep ContinueEval in
               EvaluatedDeep = {EvaluateDeep FinalResult FinalBodyProg}
               {System.showInfo ">>> EvaluatedDeep result: "#{Value.toVirtualString EvaluatedDeep 0 0}}
               case EvaluatedDeep
               of leaf(num:N) then
                  {System.showInfo ">>> EvaluatedDeep is leaf(num), returning integer: "#N}
                  N
               [] app(function:_ arg:_) then
                  {System.showInfo ">>> EvaluatedDeep is still app, continuing evaluation"}
                  ContinueEval = {Evaluate prog(function:Prog.function args:Prog.args body:Prog.body call:EvaluatedDeep)}
                  {System.showInfo ">>> ContinueEval result: "#{Value.toVirtualString ContinueEval 0 0}}
                  case ContinueEval
                  of leaf(num:N) then
                     {System.showInfo ">>> ContinueEval is leaf(num), returning integer: "#N}
                     N
                  [] N andthen {IsInt N} then
                     {System.showInfo ">>> ContinueEval is integer: "#N}
                     N
                  [] app(function:_ arg:_) then
                     {System.showInfo ">>> ContinueEval is still app, calling EvaluateDeep again"}
                     local FinalEval in
                        FinalEval = {EvaluateDeep ContinueEval prog(function:Prog.function args:Prog.args body:Prog.body call:ContinueEval)}
                        {System.showInfo ">>> FinalEval result: "#{Value.toVirtualString FinalEval 0 0}}
                        case FinalEval
                        of leaf(num:N) then N
                        [] N andthen {IsInt N} then N
                        [] _ then FinalEval
                        end
                     end
                  [] _ then ContinueEval
                  end
               [] N andthen {IsInt N} then
                  {System.showInfo ">>> EvaluatedDeep is integer: "#N}
                  N
               [] _ then
                  {System.showInfo ">>> EvaluatedDeep is not app/num, returning as-is"}
                  EvaluatedDeep
               end
            end
         [] _ then
            {System.showInfo ">>> FinalResult is other type, returning as-is"}
            FinalResult
         end
      end
   [] bind(var:V expr:E)|Rest then
      {System.showInfo ">>> Processing binding: var "#{Value.toVirtualString V 0 0}#" = "#{Value.toVirtualString E 0 0}}
      local EvaluatedExpr TempProg in
         TempProg = prog(function:Prog.function args:Prog.args body:Prog.body call:E)
         {System.showInfo ">>> Evaluating expression for var "#{Value.toVirtualString V 0 0}#": "#{Value.toVirtualString E 0 0}}
         EvaluatedExpr = {Evaluate TempProg}
         {System.showInfo ">>> EvaluatedExpr result: "#{Value.toVirtualString EvaluatedExpr 0 0}}
         case EvaluatedExpr
         of leaf(num:N) then
            {System.showInfo ">>> EvaluatedExpr is leaf(num): "#N#", substituting in body"}
            local NewRest NewBody in
               NewRest = {Map Rest fun {$ B} 
                  bind(var:B.var expr:{Subst B.expr V leaf(num:N)})
               end}
               NewBody = {Subst Body V leaf(num:N)}
               {System.showInfo ">>> NewBody after substitution: "#{Value.toVirtualString NewBody 0 0}}
               {EvalVarBindings NewRest NewBody Prog}
            end
         [] N andthen {IsInt N} then
            {System.showInfo ">>> EvaluatedExpr is integer: "#N#", converting to leaf(num) and substituting in body"}
            local NewRest NewBody in
               NewRest = {Map Rest fun {$ B} 
                  bind(var:B.var expr:{Subst B.expr V leaf(num:N)})
               end}
               NewBody = {Subst Body V leaf(num:N)}
               {System.showInfo ">>> NewBody after substitution: "#{Value.toVirtualString NewBody 0 0}}
               {EvalVarBindings NewRest NewBody Prog}
            end
         [] app(function:_ arg:_) then
            {System.showInfo ">>> EvaluatedExpr is app, calling EvaluateDeep"}
            local EvaluatedDeep FinalValue in
               EvaluatedDeep = {EvaluateDeep EvaluatedExpr TempProg}
               {System.showInfo ">>> EvaluatedDeep result: "#{Value.toVirtualString EvaluatedDeep 0 0}}
               case EvaluatedDeep
               of leaf(num:N) then
                  {System.showInfo ">>> EvaluatedDeep is number: "#N}
                  FinalValue = EvaluatedDeep
               [] app(function:_ arg:_) then
                  {System.showInfo ">>> EvaluatedDeep is still app, continuing evaluation"}
                  local ContinueEval in
                     ContinueEval = {Evaluate prog(function:Prog.function args:Prog.args body:Prog.body call:EvaluatedDeep)}
                     {System.showInfo ">>> ContinueEval result: "#{Value.toVirtualString ContinueEval 0 0}}
                     case ContinueEval
                     of leaf(num:N) then
                        {System.showInfo ">>> ContinueEval is leaf(num): "#N}
                        FinalValue = ContinueEval
                     [] N andthen {IsInt N} then
                        {System.showInfo ">>> ContinueEval is integer: "#N#", converting to leaf(num)"}
                        FinalValue = leaf(num:N)
                     [] app(function:_ arg:_) then
                        {System.showInfo ">>> ContinueEval is still app, calling EvaluateDeep again"}
                        local FinalDeep in
                           FinalDeep = {EvaluateDeep ContinueEval prog(function:Prog.function args:Prog.args body:Prog.body call:ContinueEval)}
                           {System.showInfo ">>> FinalDeep result: "#{Value.toVirtualString FinalDeep 0 0}}
                           case FinalDeep
                           of leaf(num:N) then FinalValue = FinalDeep
                           [] N andthen {IsInt N} then FinalValue = leaf(num:N)
                           [] _ then FinalValue = FinalDeep
                           end
                        end
                     [] _ then FinalValue = ContinueEval
                     end
                  end
               [] _ then
                  {System.showInfo ">>> EvaluatedDeep is not app/num, using as-is"}
                  FinalValue = EvaluatedDeep
               end
               {System.showInfo ">>> FinalValue for substitution: "#{Value.toVirtualString FinalValue 0 0}}
               case FinalValue
               of leaf(num:N) then
                  {System.showInfo ">>> FinalValue is leaf(num): "#N#", substituting in body"}
                  local NewRest NewBody in
                     NewRest = {Map Rest fun {$ B} 
                        bind(var:B.var expr:{Subst B.expr V leaf(num:N)})
                     end}
                     NewBody = {Subst Body V leaf(num:N)}
                     {System.showInfo ">>> NewBody after substitution: "#{Value.toVirtualString NewBody 0 0}}
                     {EvalVarBindings NewRest NewBody Prog}
                  end
               [] N andthen {IsInt N} then
                  {System.showInfo ">>> FinalValue is integer: "#N#", converting to leaf(num) and substituting in body"}
                  local NewRest NewBody in
                     NewRest = {Map Rest fun {$ B} 
                        bind(var:B.var expr:{Subst B.expr V leaf(num:N)})
                     end}
                     NewBody = {Subst Body V leaf(num:N)}
                     {System.showInfo ">>> NewBody after substitution: "#{Value.toVirtualString NewBody 0 0}}
                     {EvalVarBindings NewRest NewBody Prog}
                  end
               [] _ then
                  {System.showInfo ">>> FinalValue is not number, substituting as-is in body"}
                  local NewRest NewBody in
                     NewRest = {Map Rest fun {$ B} 
                        bind(var:B.var expr:{Subst B.expr V FinalValue})
                     end}
                     NewBody = {Subst Body V FinalValue}
                     {System.showInfo ">>> NewBody after substitution: "#{Value.toVirtualString NewBody 0 0}}
                     {EvalVarBindings NewRest NewBody Prog}
                  end
               end
            end
         [] _ then
            {System.showInfo ">>> EvaluatedExpr is other type, substituting as-is"}
            local NewRest NewBody in
               NewRest = {Map Rest fun {$ B} 
                  bind(var:B.var expr:{Subst B.expr V EvaluatedExpr})
               end}
               NewBody = {Subst Body V EvaluatedExpr}
               {System.showInfo ">>> NewBody after substitution: "#{Value.toVirtualString NewBody 0 0}}
               {EvalVarBindings NewRest NewBody Prog}
            end
         end
      end
   end
end

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

fun {EvalToNum Expr Prog}
   {System.showInfo "=== DEBUG EvalToNum ==="}
   {System.showInfo "Expr: "#{Value.toVirtualString Expr 0 0}}
   case Expr
   of leaf(num:N) then
      {System.showInfo ">>> EvalToNum: Expr is leaf(num), returning: "#N}
      N
   [] leaf(var:V) then
      {System.showInfo ">>> EvalToNum: Expr is variable, raising error"}
      raise error('expected_number'(expr:Expr status:whnf)) end
   [] var(bindings:Bs body:B) then
      {System.showInfo ">>> EvalToNum: Expr is var, calling EvalVarBindings"}
      local EvaluatedBody in
         EvaluatedBody = {EvalVarBindings Bs B Prog}
         {System.showInfo ">>> EvalToNum: EvalVarBindings returned: "#{Value.toVirtualString EvaluatedBody 0 0}}
         {EvalToNum EvaluatedBody Prog}
      end
   [] app(function:_ arg:_) then
      {System.showInfo ">>> EvalToNum: Expr is app, calling NextReduction"}
      local P R P2 in
         P  = prog(function:Prog.function args:Prog.args body:Prog.body call:Expr)
         R  = {NextReduction P}
         {System.showInfo ">>> EvalToNum: NextReduction status: "#{Value.toVirtualString R.status 0 0}}
         if R.status == ok then
            {System.showInfo ">>> EvalToNum: Status is ok, calling Reduce"}
            P2 = {Reduce P}
            {System.showInfo ">>> EvalToNum: After Reduce, P2.call: "#{Value.toVirtualString P2.call 0 0}#" vs P.call: "#{Value.toVirtualString P.call 0 0}}
            if P2.call == P.call then
               {System.showInfo ">>> EvalToNum: P2.call == P.call, raising stuck_in_evaltonum error"}
               raise error('stuck_in_evaltonum'(expr:Expr)) end
            else
               {System.showInfo ">>> EvalToNum: P2.call != P.call, recursively calling EvalToNum"}
               {EvalToNum P2.call P2}
            end
         elseif R.status == whnf then
            {System.showInfo ">>> EvalToNum: Status is whnf, raising expected_number error"}
            raise error('expected_number'(expr:Expr status:R.status)) end
         else
            {System.showInfo ">>> EvalToNum: Status is stuck, raising expected_number error"}
            raise error('expected_number'(expr:Expr status:R.status)) end
         end
      end
   else
      {System.showInfo ">>> EvalToNum: Expr is unexpected type, raising error"}
      raise error('unexpected_expr_in_evaltonum'(expr:Expr)) end
   end
end

fun {Reduce Prog}
   {System.showInfo "=== DEBUG Reduce ==="}
   {System.showInfo "Prog.call: "#{Value.toVirtualString Prog.call 0 0}}
   local R NewNode NewCall in
      R = {NextReduction Prog}
      {System.showInfo ">>> NextReduction status: "#{Value.toVirtualString R.status 0 0}#", kind: "#{Value.toVirtualString R.kind 0 0}}
      if R.status \= ok then
         {System.showInfo ">>> Status is not ok, returning Prog unchanged"}
         Prog
      else
         case R.kind
         of supercombinator(Fn) then
            {System.showInfo ">>> Reducing supercombinator: "#{Value.toVirtualString Fn 0 0}}
            {System.showInfo ">>> Args: "#{Value.toVirtualString Prog.args 0 0}#" with values: "#{Value.toVirtualString R.args 0 0}}
            local SubstMultiple in
               fun {SubstMultiple Expr ArgsNames ArgsValues}
                  case ArgsNames#ArgsValues
                  of nil#nil then Expr
                  [] (Name|RestNames)#(Value|RestValues) then
                     {SubstMultiple {Subst Expr Name Value} RestNames RestValues}
                  [] _#_ then Expr
                  end
               end
               local Instanced in
                  Instanced = {SubstMultiple Prog.body Prog.args R.args}
                  {System.showInfo ">>> Instanced body: "#{Value.toVirtualString Instanced 0 0}}
                  NewNode = {ApplyRest Instanced R.rest}
                  {System.showInfo ">>> NewNode after ApplyRest: "#{Value.toVirtualString NewNode 0 0}}
               end
            end            
         [] primitive(Op) then
            {System.showInfo ">>> Reducing primitive: "#{Value.toVirtualString Op 0 0}}
            local A1 A2 N1 N2 Res in
               A1 = {List.nth R.args 1}
               A2 = {List.nth R.args 2}
               {System.showInfo ">>> Primitive args: A1="#{Value.toVirtualString A1 0 0}#", A2="#{Value.toVirtualString A2 0 0}}
               try
                  N1 = {EvalToNum A1 Prog}
                  N2 = {EvalToNum A2 Prog}
                  {System.showInfo ">>> Evaluated to numbers: N1="#N1#", N2="#N2#""}
                  if Op=='rad' then
                     {System.showInfo ">>> Processing rad operation: base="#N1#", index="#N2#""}
                     if N2 == 0 then
                        {System.showInfo ">>> ERROR: zero_root_not_allowed, base="#N1#""}
                        raise error('zero_root_not_allowed'(base:N1)) end
                     else
                        local Rv in
                           Rv = {Float.pow {Int.toFloat N1} (1.0/{Int.toFloat N2})}
                           {System.showInfo ">>> rad intermediate result: "#Rv#""}
                           if Rv \= Rv orelse Rv == ~1.0/0.0 then
                              {System.showInfo ">>> ERROR: invalid_rad_result, base="#N1#", index="#N2#""}
                              raise error('invalid_rad_result'(base:N1 index:N2)) end
                           else
                              Res = {Float.toInt Rv}
                              {System.showInfo ">>> rad final result: "#Res#""}
                           end
                        end
                     end
                  else
                     {System.showInfo ">>> Processing arithmetic operation: "#{Value.toVirtualString Op 0 0}#""}
                     Res =
                        case Op
                        of '+' then
                           {System.showInfo ">>> Addition: "#N1#" + "#N2#""}
                           N1+N2
                        [] '-' then
                           {System.showInfo ">>> Subtraction: "#N1#" - "#N2#""}
                           N1-N2
                        [] '*' then
                           {System.showInfo ">>> Multiplication: "#N1#" * "#N2#""}
                           N1*N2
                        [] '/' then
                           {System.showInfo ">>> Division: "#N1#" / "#N2#""}
                           if N2 == 0 then
                              {System.showInfo ">>> ERROR: division_by_zero, dividend="#N1#""}
                              raise error('division_by_zero'(dividend:N1)) end
                           else
                              local DivResult in
                                 DivResult = N1 div N2
                                 {System.showInfo ">>> Division result: "#DivResult#""}
                                 DivResult
                              end
                           end
                        else
                           {System.showInfo ">>> ERROR: unknown_operator: "#{Value.toVirtualString Op 0 0}#""}
                           raise error('unknown_operator'(op:Op)) end
                        end
                  end
                  {System.showInfo ">>> Primitive result: "#Res#""}
                  NewNode = {ApplyRest leaf(num:Res) R.rest}
                  {System.showInfo ">>> NewNode after ApplyRest: "#{Value.toVirtualString NewNode 0 0}}
               catch E then
                  {System.showInfo ">>> EXCEPTION CAUGHT in primitive reduction: "#{Value.toVirtualString E 0 0}}
                  {System.showInfo ">>> Exception type: "#{Value.toVirtualString {Label E} 0 0}#""}
                  {System.showInfo ">>> Keeping R.root unchanged: "#{Value.toVirtualString R.root 0 0}}
                  NewNode = R.root
               end
            end         
         else
            {System.showInfo ">>> Unknown reduction kind, using R.head"}
            NewNode = R.head
         end

         {System.showInfo ">>> Replacing R.root: "#{Value.toVirtualString R.root 0 0}#" with NewNode: "#{Value.toVirtualString NewNode 0 0}}
         NewCall = {ReplaceSub Prog.call R.root NewNode}
         {System.showInfo ">>> NewCall after ReplaceSub: "#{Value.toVirtualString NewCall 0 0}}
         prog(function:Prog.function args:Prog.args body:Prog.body call:NewCall)
      end
   end
end


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Task 4
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fun {Evaluate Prog}
   {System.showInfo "=== DEBUG Evaluate ==="}
   {System.showInfo "Prog.call: "#{Value.toVirtualString Prog.call 0 0}}
   case Prog.call
   of leaf(num:N) then
      {System.showInfo ">>> Evaluate: call is number, returning: "#N}
      N
   [] _ then
      local R Pnext in
         R = {NextReduction Prog}
         {System.showInfo ">>> NextReduction status: "#{Value.toVirtualString R.status 0 0}}
         if R.status == ok then
            {System.showInfo ">>> Status is ok, calling Reduce"}
            Pnext = {Reduce Prog}
            {System.showInfo ">>> After Reduce, Pnext.call: "#{Value.toVirtualString Pnext.call 0 0}}
            local PnextCall ProgCall in
               PnextCall = Pnext.call
               ProgCall = Prog.call
               if {Value.isDet PnextCall} andthen {Value.isDet ProgCall} andthen PnextCall == ProgCall then
                  {System.showInfo ">>> Pnext.call == Prog.call, checking if number"}
                  case ProgCall
                  of leaf(num:N) then
                     {System.showInfo ">>> Returning number: "#N}
                     N
                  [] _ then
                     {System.showInfo ">>> Returning ProgCall as-is: "#{Value.toVirtualString ProgCall 0 0}}
                     ProgCall
                  end
               else
                  {System.showInfo ">>> Pnext.call != Prog.call, recursively evaluating"}
                  {Evaluate Pnext}
               end
            end         

         elseif R.status == whnf then
            {System.showInfo ">>> Status is whnf, handling WHNF case"}
            local Normal in
               case Prog.call
               of var(bindings:Bs body:B) then
                  {System.showInfo ">>> Call is var, calling EvalVarBindings"}
                  Normal = {EvalVarBindings Bs B Prog}
                  {System.showInfo ">>> EvalVarBindings returned: "#{Value.toVirtualString Normal 0 0}}
               [] _ then
                  {System.showInfo ">>> Call is not var, calling EvaluateDeep"}
                  Normal = {EvaluateDeep Prog.call Prog}
                  {System.showInfo ">>> EvaluateDeep returned: "#{Value.toVirtualString Normal 0 0}}
               end
         
               local NormalCall ProgCall in
                  NormalCall = Normal
                  ProgCall = Prog.call
                  {System.showInfo ">>> NormalCall: "#{Value.toVirtualString NormalCall 0 0}#" vs ProgCall: "#{Value.toVirtualString ProgCall 0 0}}
                  if {Value.isDet NormalCall} andthen {Value.isDet ProgCall} andthen NormalCall == ProgCall then
                     {System.showInfo ">>> NormalCall == ProgCall, returning ProgCall"}
                     ProgCall
                  else
                     {System.showInfo ">>> NormalCall != ProgCall, recursively evaluating with NormalCall"}
                     {Evaluate prog(function:Prog.function args:Prog.args body:Prog.body call:NormalCall)}
                  end
               end
            end 
         else
            {System.showInfo ">>> Status is stuck, handling stuck case"}
            case Prog.call
            of leaf(num:N) then
               {System.showInfo ">>> Stuck but call is number, returning: "#N}
               N
            [] var(bindings:Bs body:B) then
               {System.showInfo ">>> Stuck and call is var, calling EvalVarBindings"}
               local EvalResult in
                  EvalResult = {EvalVarBindings Bs B Prog}
                  {System.showInfo ">>> EvalVarBindings returned: "#{Value.toVirtualString EvalResult 0 0}}
                  case EvalResult
                  of leaf(num:_) then EvalResult
                  [] app(function:_ arg:_) then
                     {Evaluate prog(function:Prog.function args:Prog.args body:Prog.body call:EvalResult)}
                  [] _ then EvalResult
                  end
               end
            [] _ then
               {System.showInfo ">>> Stuck, returning call as-is: "#{Value.toVirtualString Prog.call 0 0}}
               Prog.call
            end
         end
      end
   end
end

fun {EvaluateDeep Expr Prog}
   {System.showInfo "=== DEBUG EvaluateDeep ==="}
   {System.showInfo "Expr: "#{Value.toVirtualString Expr 0 0}}
   case Expr
   of leaf(num:N) then
      {System.showInfo ">>> EvaluateDeep: Expr is number, returning"}
      Expr
   [] leaf(var:_) then
      {System.showInfo ">>> EvaluateDeep: Expr is variable, returning as-is"}
      Expr
   [] app(function:F arg:A) then
      {System.showInfo ">>> EvaluateDeep: Expr is app, evaluating F and A"}
      local EvaluatedF EvaluatedA Combined in
         EvaluatedF = {EvaluateDeep F Prog}
         {System.showInfo ">>> EvaluatedF: "#{Value.toVirtualString EvaluatedF 0 0}}
         EvaluatedA = {EvaluateDeep A Prog}
         {System.showInfo ">>> EvaluatedA: "#{Value.toVirtualString EvaluatedA 0 0}}
         Combined = app(function:EvaluatedF arg:EvaluatedA)
         {System.showInfo ">>> Combined: "#{Value.toVirtualString Combined 0 0}}
         local TempProg R Reduced in
            TempProg = prog(function:Prog.function args:Prog.args body:Prog.body call:Combined)
            R = {NextReduction TempProg}
            {System.showInfo ">>> NextReduction status: "#{Value.toVirtualString R.status 0 0}}
            if R.status == ok then
               {System.showInfo ">>> Status is ok, calling Reduce"}
               Reduced = {Reduce TempProg}
               {System.showInfo ">>> After Reduce, Reduced.call: "#{Value.toVirtualString Reduced.call 0 0}}
               local ReducedCall in
                  ReducedCall = Reduced.call
                  if {Value.isDet ReducedCall} andthen {Value.isDet Combined} andthen ReducedCall == Combined then
                     {System.showInfo ">>> ReducedCall == Combined, returning Combined"}
                     Combined
                  else
                     {System.showInfo ">>> ReducedCall != Combined, checking type"}
                     case ReducedCall
                     of leaf(num:_) then
                        {System.showInfo ">>> ReducedCall is number, returning"}
                        ReducedCall
                     [] app(function:_ arg:_) then
                        {System.showInfo ">>> ReducedCall is still app, recursively calling EvaluateDeep"}
                        {EvaluateDeep ReducedCall Reduced}
                     [] _ then
                        {System.showInfo ">>> ReducedCall is other type, returning as-is"}
                        ReducedCall
                     end
                  end
               end
            else
               {System.showInfo ">>> Status is not ok, returning Combined"}
               Combined
            end
         end
      end
   [] var(bindings:Bs body:B) then
      {System.showInfo ">>> EvaluateDeep: Expr is var, calling EvalVarBindings"}
      {EvaluateDeep {EvalVarBindings Bs B Prog} Prog}
   else
      {System.showInfo ">>> EvaluateDeep: Expr is other type, returning as-is"}
      Expr
   end
end

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 🔥🔥🔥 SUPER TEST CASE ULTRA COMPLETO
%%   Cubre: + - * /, var, nested var, múltiples parámetros,
%%          WHNF, stuck, infix/prefix, parentheses,
%%          overapplication, underapplication, combinaciones,
%%          prioridad de operadores, estructuras absurdas.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %% 1. Aritmética básica + precedencia + paréntesis
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   
   {System.showInfo "TEST S1: (3 + 4) * (10 - 2) = 56"}
   {System.showInfo ">>> About to call GraphGeneration for S1"}
   local P1 R1 in
      P1 = {GraphGeneration "fun f x = (3 + 4) * (10 - 2)\nf 0"}
      {System.showInfo ">>> GraphGeneration S1 returned, P1 = "#{Value.toVirtualString P1 0 0}}
      {System.showInfo ">>> About to call Evaluate for S1"}
   R1 = {Evaluate P1}
      {System.showInfo ">>> Evaluate S1 returned"}
   {PrintResult R1}
   end
   
   {System.showInfo "TEST S2: 3 + 4 * 10 = 43"}
   {System.showInfo ">>> About to call GraphGeneration for S2"}
   local P2 in
      P2 = {GraphGeneration "fun f x = 3 + 4 * 10\nf 0"}
      {System.showInfo ">>> GraphGeneration S2 returned, P2 = "#{Value.toVirtualString P2 0 0}}
      {System.showInfo ">>> About to call Evaluate for S2"}
      {PrintResult {Evaluate P2}}
   end
   
   {System.showInfo "TEST S3: (3 + 4) * 10 = 70"}
   local P3 in
      P3 = {GraphGeneration "fun f x = (3 + 4) * 10\nf 0"}
      {PrintResult {Evaluate P3}}
   end
   
   {System.showInfo "TEST S4: 100 / 5 / 2 = 10 (left associative)"}
   local P4 in
      P4 = {GraphGeneration "fun f x = 100 / 5 / 2\nf 0"}
      {PrintResult {Evaluate P4}}
   end
   
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %% 2. Supercombinators multi-parámetro
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   
   {System.showInfo "TEST S5: fun add3 a b c = a + b + c"}
   local P5 in
      P5 = {GraphGeneration "fun add3 a b c = a + b + c\nadd3 5 6 7"}
      {PrintResult {Evaluate P5}}
   end
   
   {System.showInfo "TEST S6: fun weird x y z = (x * y) - (y / z)"}
   local P6 in
      P6 = {GraphGeneration "fun weird x y z = (x * y) - (y / z)\nweird 10 6 3"}
      {PrintResult {Evaluate P6}}
   end
   
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %% 3. Internal variables (var ... in ...)
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   
   {System.showInfo "TEST S7: var simple binding"}
   local P7 in
      P7 = {GraphGeneration "fun g x = var y = x + 1 in y * 10\ng 7"}
      {PrintResult {Evaluate P7}}
   end
   
   {System.showInfo "TEST S8: nested var + arithmetic"}
   local P8 in
      P8 = {GraphGeneration "fun g x = var a = x * x in var b = a + 10 in b / 2\ng 4"}
      {PrintResult {Evaluate P8}}
   end
   
   {System.showInfo "TEST S9: deeply nested var + parentheses"}
   local P9 in
      P9 = {GraphGeneration "fun h x = var a = (x + 1) in var b = (a * 2) in var c = (b - 3) in c + a\nh 5"}
      {PrintResult {Evaluate P9}}
   end
   
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %% 4. Overapplication & Underapplication (WHNF)
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   
   {System.showInfo "TEST S10: Underapplication of + → WHNF"}
   local P10 in
      P10 = prog(function:'f' args:[x]
                 body:leaf(var:x)
                 call:app(function:leaf(var:'+') arg:leaf(num:3)))
      {PrintResult {Evaluate P10}}   %% EXPECT: stuck in WHNF
   end
   
   {System.showInfo "TEST S11: Overapplication: f x y = x+y; call f 5 6 7"}
   local P11 in
      P11 = {GraphGeneration "fun f x y = x + y\nf 5 6 7"}
      {PrintResult {Evaluate P11}}   %% last arg (7) is applied to a number → stuck
   end
   
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %% 5. Function calls nested arbitrarily
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   
   {System.showInfo "TEST S12: cascaded calls f (f (f 3))"}
   local P12 in
      P12 = {GraphGeneration "fun f x = x * 2\nf f f 3"}
      {PrintResult {Evaluate P12}}  %% (((f f) f) 3)
   end
   
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %% 6. Division edge cases
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   
   {System.showInfo "TEST S13: division by zero handoff (should remain stuck)"}
   local P13 in
      P13 = {GraphGeneration "fun f x = 10 / 0\nf 0"}
      {PrintResult {Evaluate P13}}   %% Should not crash; WHNF or stuck
   end
   
   {System.showInfo "TEST S14: inside var binding division by zero"}
   local P14 in
      P14 = {GraphGeneration "fun f x = var y = 10 / 0 in y + 3\nf 0"}
      {PrintResult {Evaluate P14}}   %% WHNF for y
   end
   
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %% 7. Complex infix + prefix mix
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   
   {System.showInfo "TEST S15: prefix operator-style: + 3 5"}
   local P15 in
      P15 = {GraphGeneration "fun f x = + 3 5\nf 0"}
      {PrintResult {Evaluate P15}}
   end
   
   {System.showInfo "TEST S16: mixed: + (3 * 4) 10"}
   local P16 in
      P16 = {GraphGeneration "fun f x = + (3 * 4) 10\nf 0"}
      {PrintResult {Evaluate P16}}
   end
   
   {System.showInfo "TEST S17: nested mixed hell: + 2 (3 * (4 + 5) / (2 - 1))"}
   local P17 in
      P17 = {GraphGeneration "fun f x = + 2 (3 * (4 + 5) / (2 - 1))\nf 0"}
      {PrintResult {Evaluate P17}}
   end
   
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %% 8. WHNF variable propagation
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   
   {System.showInfo "TEST S18: x + y with y unknown → WHNF"}
   local P18 in
      P18 = {GraphGeneration "fun bad x = x + y\nbad 3"}
      {PrintResult {Evaluate P18}}
   end
   
   {System.showInfo "TEST S19: return internal var without reducing"}
   local P19 in
      P19 = {GraphGeneration "fun t x = var y = x + 1 in y\nt 10"}
      {PrintResult {Evaluate P19}}
   end
   
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %% 9. Strange structures / parenthesis abuse
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   
   {System.showInfo "TEST S20: (((((3)))) + (((((4)))))) = 7"}
   local P20 in
      P20 = {GraphGeneration "fun f x = (((((3)))) + (((((4))))))\nf 0"}
      {PrintResult {Evaluate P20}}
   end
   
   {System.showInfo "TEST S21: ((((x))))"}
   local P21 in
      P21 = {GraphGeneration "fun f x = (((x)))\nf 9"}
      {PrintResult {Evaluate P21}}
   end
   
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %% 10. Stress test: monstrous nested ops
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   
   {System.showInfo "TEST S22: MONSTER EXPRESSION"}
   local P22 in
      P22 = {GraphGeneration "fun f x = (((x + 1) * (x + 2)) / (x - 3)) + ((x * x) - (10 / (x - 5)))\nf 10"}
      {PrintResult {Evaluate P22}}
   end
   
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   %% 11. Argumentos repetidos / Shadowing real (var x oculta parámetro x) / Encadenamiento estricto var→var→var
   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
   
   {System.showInfo "TEST S23: duplicated arguments (x used twice) EXPECTED: 20"}
   local P23 in
      P23 = {GraphGeneration "fun dup x y = x + x + y\ndup 5 10"}
      {PrintResult {Evaluate P23}}   %% EXPECTED: 20
   end
   
   {System.showInfo "TEST S24: shadowing — var x shadows function parameter x EXPECTED: 20"}
   local P24 in
      P24 = {GraphGeneration "fun f x = var x = 10 in x + x\nf 3"}
      {PrintResult {Evaluate P24}}   %% EXPECTED: 20
   end
   
   {System.showInfo "TEST S25: chained var dependencies (a→b→c) EXPECTED: 12"}
   local P25 in
      P25 = {GraphGeneration "fun chain x = var a = x + 1 in var b = a * 2 in var c = b - a in c + b\nchain 3"}
      {PrintResult {Evaluate P25}}   %% EXPECTED: 12
   end