%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Template Instantiation - Basic Implementation
%% Based on the project specification
%% 
%% The objective of this project is to use Mozart to build a very tiny 
%% functional programming language (the base to build any functional language).
%% The project develops the initial approach to implement functional programming,
%% which consists of a graph reduction technique called template instantiation.
%%
%% The idea of template instantiation is to represent expressions (program 
%% instructions) as a graph, and apply the outermost reductions to evaluate 
%% the expression.
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
            elseif C==&+ orelse C==&- orelse C==&* orelse C==&/ then
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
%% Task 1: Graph Generation
%% Build the graph to represent the program
%% Graph consists of:
%% 1. Leaf nodes: constants (numbers) or variables
%% 2. Application nodes (@): function applications
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
   fun {Loop Ts Out Stk}
      case Ts
      of nil then {Append Out Stk}
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
               {Loop Tr {Append Out Out2} T|S2}
            end
         else
            {Loop Tr {Append Out [T]} Stk}
         end
      end
   end
in
   {Loop Tokens nil nil}
end

fun {RPNtoAST RPN}
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
         of [X] then X
         [] _ then raise error('rpn_final_stack') end
         end
      [] Tok|Tr then
         if {IsOp Tok} then
            local A B Rest NewNode in
               A#B#Rest = {Pop2 Stk}
               NewNode = app(function:app(function:leaf(var:Tok) arg:B) arg:A)
               {Loop Tr {Push Rest NewNode}}
            end
         else
            local LeafNode in
               LeafNode = {Leaf Tok}
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
   local
      %% Helper to process parentheses: find matching close paren
      fun {ProcessParens Ts}
         local
            fun {FindClose Ts Acc Depth}
               case Ts
               of nil then raise error('unmatched_parens') end
               [] '('|Tr then {FindClose Tr Acc Depth+1}
               [] ')'|Tr then
                  if Depth == 1 then
                     {List.reverse Acc}#Tr
                  else
                     {FindClose Tr ')'|Acc Depth-1}
                  end
               [] T|Tr then {FindClose Tr T|Acc Depth}
               end
            end
            
      fun {ProcessTokens Ts Acc}
               case Ts
               of nil then {List.reverse Acc}
               [] '('|Tr then
                  local Content Rest ProcessedContent in
                     Content#Rest = {FindClose Tr nil 1}
                     ProcessedContent = {BuildExpr Content}
                     %% Use prepend to maintain consistency with other tokens
                     {ProcessTokens Rest ProcessedContent|Acc}
                  end
               [] ')'|Tr then
                  %% Skip closing parens that don't match (shouldn't happen, but handle gracefully)
                  {ProcessTokens Tr Acc}
               [] T|Tr then
                  {ProcessTokens Tr T|Acc}
               end
      end
   in
      {ProcessTokens Ts nil}
         end
      end
      
      fun {IsASTNode X}
         try
            case X
            of app(function:_ arg:_) then true
            [] leaf(_) then true
            [] var(bindings:_ body:_) then true
            else
               %% Check if it's a record with label 'app', 'leaf', or 'var'
               local L in
                  L = {Label X}
                  L == 'app' orelse L == 'leaf' orelse L == 'var'
               end
            end
         catch _ then false
         end
      end
      
      fun {BuildLeftWithExprs Ts}
         %% Filter out any remaining parentheses (shouldn't happen, but handle gracefully)
         local Filtered in
            Filtered = {List.filter Ts fun {$ T} T \= '(' andthen T \= ')' end}
            case Filtered
            of nil then raise error('empty_expression') end
            [] [X] then
               %% If X is already an AST node, return it directly
               try
                  case X
                  of app(function:_ arg:_) then X
                  [] leaf(_) then X
                  [] var(bindings:_ body:_) then X
                  else
                     %% Try to check label
                     local L in
                        L = {Label X}
                        if L == 'app' orelse L == 'leaf' orelse L == 'var' then
                           X
                        else
                           {Leaf X}
                        end
                     end
                  end
               catch _ then {Leaf X}
               end
            [] H|T then
               local
                  FirstExpr = try
                                 case H
                                 of app(function:_ arg:_) then H
                                 [] leaf(_) then H
                                 [] var(bindings:_ body:_) then H
                                 else
                                    local L in
                                       L = {Label H}
                                       if L == 'app' orelse L == 'leaf' orelse L == 'var' then
                                          H
                                       else
                                          {Leaf H}
                                       end
                                    end
                                 end
                              catch _ then {Leaf H}
                              end
               in
                  {BuildLeftFrom FirstExpr T}
               end
            end
         end
      end
      
      fun {BuildLeftFrom F Ts}
         %% Filter out any remaining parentheses (shouldn't happen, but handle gracefully)
         local Filtered in
            Filtered = {List.filter Ts fun {$ T} T \= '(' andthen T \= ')' end}
            case Filtered
            of nil then F
            [] H|T then
               local
                  ArgExpr = if {IsASTNode H} then
                               H
                            else
                               {Leaf H}
                            end
               in
                  {BuildLeftFrom app(function:F arg:ArgExpr) T}
               end
            end
         end
      end
   in
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
         {RPNtoAST {ToRPN Xs}}
      else
            local ProcessedTokens in
               ProcessedTokens = {ProcessParens Xs}
               %% If ProcessParens returned a single AST node, return it directly
               case ProcessedTokens
               of [X] then
                  try
                     case X
                     of app(function:_ arg:_) then X
                     [] leaf(_) then X
                     [] var(bindings:_ body:_) then X
                     else
                        local L in
                           L = {Label X}
                           if L == 'app' orelse L == 'leaf' orelse L == 'var' then
                              X
                           else
                              {BuildLeftWithExprs ProcessedTokens}
                           end
                        end
                     end
                  catch _ then
                     {BuildLeftWithExprs ProcessedTokens}
                  end
               else
                  {BuildLeftWithExprs ProcessedTokens}
               end
            end
         end
      end   
   end
end

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

      FunBody   = {BuildExpr BodyTokens}
      CallGraph = {BuildExpr TokensCall}

      prog(function:FName args:ArgsTokens body:FunBody call:CallGraph)
   end
end

%% ────────────────────────────────────────────────
%% Task 2: Next Redex
%% Find the next expression to reduce.
%% The expression to reduce must always be the outermost expression in the tree.
%% 1. Follow the left branch of the application nodes, starting at the root,
%%    until you get to a supercombinator or built-in primitive.
%% ────────────────────────────────────────────────

fun {IsPrimitive Op}
   {List.member Op ['+' '-' '*' '/']}
end
 
 fun {HeadArity Head Prog}
    case Head
    of leaf(var:Op) then
      if {IsPrimitive Op} then
         2
      elseif Op==Prog.function then
         {Length Prog.args}
      else
         0
      end
   [] leaf(num:_) then
      0
   else
      0
    end
 end
 
 fun {HeadKind Head Prog}
    case Head
    of leaf(var:Op) then
      if {IsPrimitive Op} then
         primitive(Op)
      elseif Op==Prog.function then
         supercombinator(Op)
      else
         variable(Op)
      end
   [] leaf(num:N) then
      number(N)
   else
      other
    end
 end
 
 fun {Unwind Expr Args Apps}
    case Expr
    of app(function:F arg:A) then
       {Unwind F A|Args Expr|Apps}
    else
       unwind(head:Expr args:Args apps:Apps)
    end
 end

fun {MakeApp F Args}
   case Args
   of nil then F
   [] A|Ar then {MakeApp app(function:F arg:A) Ar}
   end
end
 
fun {NextRedex Prog}
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
         Root      = {MakeApp Head ArgsK}
         redex(status:ok kind:Kind head:Head arity:K
               args:ArgsK rest:Remaining
               root:Root apps:Apps allargs:AllArgs)
      end
   end
end
 
%% ────────────────────────────────────────────────
%% Task 3: Reduce
%% Check how many arguments the supercombinator or primitive takes and 
%% go back up that number of application nodes; you have now found the 
%% root of the outermost function application. Now, reduce the expression 
%% (a.k.a evaluate). For built-in primitives you have to evaluate them, 
%% for supercombinators replace their definition into the tree.
%% ────────────────────────────────────────────────

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
      local Shadowed in
         Shadowed = {List.some Bs fun {$ B} B.var == Var end}
         if Shadowed then
            var(bindings:{Map Bs fun {$ B}
                              bind(var:B.var expr:{Subst B.expr Var WithNode})
                           end}
                body:B)
         else
            var(bindings:{Map Bs fun {$ B}
                              bind(var:B.var expr:{Subst B.expr Var WithNode})
                           end}
                body:{Subst B Var WithNode})
         end
      end
   else
      Expr
   end
end

fun {ApplyRest Node Rest}
   case Rest
   of nil then Node
   [] R|Rs then
      {ApplyRest app(function:Node arg:R) Rs}
   end
end

fun {EvalVarBindings Bindings Body Prog}
   case Bindings
   of nil then
      local FinalBodyProg FinalResult in
         FinalBodyProg = prog(function:Prog.function args:Prog.args body:Prog.body call:Body)
         FinalResult = {Evaluate FinalBodyProg}
         case FinalResult
         of leaf(num:N) then N
         [] N andthen {IsInt N} then N
         [] app(function:_ arg:_) then
            {EvaluateDeep FinalResult FinalBodyProg}
         [] _ then FinalResult
         end
      end
   [] bind(var:V expr:E)|Rest then
      local EvaluatedExpr TempProg in
         TempProg = prog(function:Prog.function args:Prog.args body:Prog.body call:E)
         EvaluatedExpr = {Evaluate TempProg}
         local NewRest NewBody FinalValue in
            FinalValue = case EvaluatedExpr
                         of leaf(num:N) then leaf(num:N)
                         [] N andthen {IsInt N} then leaf(num:N)
                         [] app(function:_ arg:_) then
                            {EvaluateDeep EvaluatedExpr TempProg}
                         [] _ then EvaluatedExpr
                         end
            NewRest = {Map Rest fun {$ B} 
                  bind(var:B.var expr:{Subst B.expr V FinalValue})
            end}
            NewBody = {Subst Body V FinalValue}
            {EvalVarBindings NewRest NewBody Prog}
         end
      end
   end
end

fun {ReplaceSub Expr Root New}
   local
      fun {ReplaceSubOnce Expr Root New Done}
         if {Value.isDet Done} andthen Done then
            Expr#Done
         elseif Expr==Root then
            New#true
   else
      case Expr
      of app(function:F arg:A) then
               local NewF DoneF NewA DoneA Result in
                  NewF#DoneF = {ReplaceSubOnce F Root New Done}
                  NewA#DoneA = {ReplaceSubOnce A Root New DoneF}
                  Result = app(function:NewF arg:NewA)
                  Result#DoneA
               end
            else
               Expr#Done
            end
         end
      end
   in
      local Result Done in
         Result#Done = {ReplaceSubOnce Expr Root New false}
         Result
      end
   end
end

fun {EvalToNum Expr Prog}
   case Expr
   of leaf(num:N) then N
   [] leaf(var:V) then
      raise error('expected_number'(expr:Expr status:whnf)) end
   [] var(bindings:Bs body:B) then
      local EvaluatedBody in
         EvaluatedBody = {EvalVarBindings Bs B Prog}
         {EvalToNum EvaluatedBody Prog}
      end
   [] app(function:_ arg:_) then
      local P R P2 in
         P  = prog(function:Prog.function args:Prog.args body:Prog.body call:Expr)
         R  = {NextRedex P}
         if R.status == ok then
            P2 = {Reduce P}
            if P2.call == P.call then
               raise error('stuck_in_evaltonum'(expr:Expr)) end
            else
               {EvalToNum P2.call P2}
            end
         else
            raise error('expected_number'(expr:Expr status:R.status)) end
         end
      end
   else
      raise error('unexpected_expr_in_evaltonum'(expr:Expr)) end
   end
end

fun {Reduce Prog}
   local R NewNode NewCall in
      R = {NextRedex Prog}
      if R.status \= ok then
         Prog
      else
         case R.kind
         of supercombinator(Fn) then
            local SubstMultiple Instanced EvaluatedInstanced in
               fun {SubstMultiple Expr ArgsNames ArgsValues}
                  case ArgsNames#ArgsValues
                  of nil#nil then Expr
                  [] (Name|RestNames)#(Value|RestValues) then
                     {SubstMultiple {Subst Expr Name Value} RestNames RestValues}
                  [] _#_ then Expr
                  end
               end
                  Instanced = {SubstMultiple Prog.body Prog.args R.args}
               local TempProgInst EvalResultInst in
                  TempProgInst = prog(function:Prog.function args:Prog.args body:Prog.body call:Instanced)
                  EvalResultInst = {Evaluate TempProgInst}
                  EvaluatedInstanced = case EvalResultInst
                                       of leaf(num:N) then leaf(num:N)
                                       [] N andthen {IsInt N} then leaf(num:N)
                                       [] app(function:_ arg:_) then
                                          {EvaluateDeep EvalResultInst TempProgInst}
                                       [] _ then EvalResultInst
                                       end
               end
               NewNode = {ApplyRest EvaluatedInstanced R.rest}
            end            
         [] primitive(Op) then
            local A1 A2 N1 N2 Res EvaluatedA1 EvaluatedA2 in
               A1 = {List.nth R.args 1}
               A2 = {List.nth R.args 2}
               try
                  EvaluatedA1 = case A1
                                of app(function:_ arg:_) then
                                   local TempProg1 EvalResult1 in
                                      TempProg1 = prog(function:Prog.function args:Prog.args body:Prog.body call:A1)
                                      EvalResult1 = {Evaluate TempProg1}
                                      case EvalResult1
                                      of leaf(num:N) then leaf(num:N)
                                      [] N andthen {IsInt N} then leaf(num:N)
                                      [] app(function:_ arg:_) then
                                         {EvaluateDeep EvalResult1 TempProg1}
                                      [] _ then EvalResult1
                           end
                        end
                                [] _ then A1
                                end
                  EvaluatedA2 = case A2
                                of app(function:_ arg:_) then
                                   local TempProg2 EvalResult2 in
                                      TempProg2 = prog(function:Prog.function args:Prog.args body:Prog.body call:A2)
                                      EvalResult2 = {Evaluate TempProg2}
                                      case EvalResult2
                                      of leaf(num:N) then leaf(num:N)
                                      [] N andthen {IsInt N} then leaf(num:N)
                                      [] app(function:_ arg:_) then
                                         {EvaluateDeep EvalResult2 TempProg2}
                                      [] _ then EvalResult2
                                      end
                                   end
                                [] _ then A2
                                end
                  N1 = {EvalToNum EvaluatedA1 Prog}
                  N2 = {EvalToNum EvaluatedA2 Prog}
                  Res = case Op
                        of '+' then N1+N2
                        [] '-' then N1-N2
                        [] '*' then N1*N2
                        [] '/' then
                           if N2 == 0 then
                              raise error('division_by_zero'(dividend:N1)) end
                           else
                              N1 div N2
                           end
                        else
                           raise error('unknown_operator'(op:Op)) end
                  end
                  NewNode = {ApplyRest leaf(num:Res) R.rest}
               catch E then
                  NewNode = R.root
               end
            end         
         else
            NewNode = R.head
         end

         local RootToReplace in
            if {Length R.rest} > 0 then
               RootToReplace = {MakeApp R.root R.rest}
            else
               RootToReplace = R.root
            end
            NewCall = {ReplaceSub Prog.call RootToReplace NewNode}
         end
         prog(function:Prog.function args:Prog.args body:Prog.body call:NewCall)
      end
   end
end

%% ────────────────────────────────────────────────
%% Task 4: Evaluate
%% Update the expression with the result of the evaluation.
%% Note that not all programs need to be reducible (for example if the 
%% evaluation is not complete as variables are not known; the reduction 
%% of the expression x + x is itself if a value for x is unknown).
%% 
%% This function is the evaluation API of the program.
%% Programs should be evaluated as {Evaluate {GraphGeneration P}}
%% to return their resulting value
%% ────────────────────────────────────────────────

fun {EvaluateDeep Expr Prog}
   case Expr
   of leaf(num:N) then
      Expr
   [] leaf(var:V) then
      Expr
   [] app(function:F arg:A) then
      local EvaluatedF EvaluatedA Combined in
         EvaluatedF = {EvaluateDeep F Prog}
         EvaluatedA = {EvaluateDeep A Prog}
         Combined = app(function:EvaluatedF arg:EvaluatedA)
         local TempProg R Reduced in
            TempProg = prog(function:Prog.function args:Prog.args body:Prog.body call:Combined)
            R = {NextRedex TempProg}
            if R.status == ok then
               Reduced = {Reduce TempProg}
               local ReducedCall in
                  ReducedCall = Reduced.call
                  if {Value.isDet ReducedCall} andthen {Value.isDet Combined} andthen ReducedCall == Combined then
                     Combined
                  else
                     case ReducedCall
                     of leaf(num:_) then ReducedCall
                     [] app(function:_ arg:_) then
                        {EvaluateDeep ReducedCall Reduced}
                     [] _ then ReducedCall
                     end
                  end
               end
            else
               Combined
            end
         end
      end
   [] var(bindings:Bs body:B) then
      {EvaluateDeep {EvalVarBindings Bs B Prog} Prog}
   else
      Expr
   end
end

fun {Evaluate Prog}
   case Prog.call
   of leaf(num:N) then
      N
   [] _ then
      local R Pnext in
         R = {NextRedex Prog}
         if R.status == ok then
            Pnext = {Reduce Prog}
            local PnextCall ProgCall in
               PnextCall = Pnext.call
               ProgCall = Prog.call
               if {Value.isDet PnextCall} andthen {Value.isDet ProgCall} andthen PnextCall == ProgCall then
                  case ProgCall
               of leaf(num:N) then N
                  [] _ then ProgCall
               end
            else
               {Evaluate Pnext}
            end         
            end         
         elseif R.status == whnf then
            local Normal in
               case Prog.call
               of var(bindings:Bs body:B) then
                  Normal = {EvalVarBindings Bs B Prog}
               [] _ then
                  Normal = {EvaluateDeep Prog.call Prog}
               end
         
               local NormalCall ProgCall in
                  NormalCall = Normal
                  ProgCall = Prog.call
                  if {Value.isDet NormalCall} andthen {Value.isDet ProgCall} andthen NormalCall == ProgCall then
                     ProgCall
                  else
                     {Evaluate prog(function:Prog.function args:Prog.args body:Prog.body call:NormalCall)}
                  end
               end
            end 
         else
            case Prog.call
            of leaf(num:N) then N
            [] var(bindings:Bs body:B) then
               local EvalResult in
                  EvalResult = {EvalVarBindings Bs B Prog}
                  case EvalResult
                  of leaf(num:_) then EvalResult
                  [] app(function:_ arg:_) then
                     {Evaluate prog(function:Prog.function args:Prog.args body:Prog.body call:EvalResult)}
                  [] _ then EvalResult
            end
         end
            [] _ then
               Prog.call
      end
   end
end
   end
end

%% ────────────────────────────────────────────────
%% Test Cases
%% ────────────────────────────────────────────────

{System.showInfo "\n=== TEST S1: fun sum_n x y z n = (x + y + z) * n ==="}
local P1 R1 in
   P1 = {GraphGeneration "fun sum_n x y z n = (x + y + z) * n\nsum_n 1 2 3 4"}
   R1 = {Evaluate P1}
   {System.showInfo "Result: "#R1#" (Expected: (1+2+3)*4 = 24)"}
end

{System.showInfo "\n=== TEST S2: 3 + 4 * 10 = 43 ==="}
local P2 R2 in
   P2 = {GraphGeneration "fun f x = 3 + 4 * 10\nf 0"}
   R2 = {Evaluate P2}
   {System.showInfo "Result: "#R2#" (Expected: 43)"}
end
   
{System.showInfo "\n=== TEST S3: (3 + 4) * 10 = 70 ==="}
local P3 R3 in
   P3 = {GraphGeneration "fun f x = (3 + 4) * 10\nf 0"}
   R3 = {Evaluate P3}
   {System.showInfo "Result: "#R3#" (Expected: 70)"}
end
   
{System.showInfo "\n=== TEST S4: 100 / 5 / 2 = 10 (left associative) ==="}
local P4 R4 in
   P4 = {GraphGeneration "fun f x = 100 / 5 / 2\nf 0"}
   R4 = {Evaluate P4}
   {System.showInfo "Result: "#R4#" (Expected: 10)"}
end
   
{System.showInfo "\n=== TEST S5: fun add3 a b c = a + b + c ==="}
local P5 R5 in
   P5 = {GraphGeneration "fun add3 a b c = a + b + c\nadd3 5 6 7"}
   R5 = {Evaluate P5}
   {System.showInfo "Result: "#R5#" (Expected: 18)"}
end

{System.showInfo "\n=== TEST S6: fun weird x y z = (x * y) - (y / z) ==="}
local P6 R6 in
   P6 = {GraphGeneration "fun weird x y z = (x * y) - (y / z)\nweird 10 6 3"}
   R6 = {Evaluate P6}
   {System.showInfo "Result: "#R6#" (Expected: (10*6) - (6/3) = 60 - 2 = 58)"}
end

{System.showInfo "\n=== TEST S7: var simple binding ==="}
local P7 R7 in
   P7 = {GraphGeneration "fun g x = var y = x + 1 in y * 10\ng 7"}
   R7 = {Evaluate P7}
   {System.showInfo "Result: "#R7#" (Expected: (7+1)*10 = 80)"}
end

{System.showInfo "\n=== TEST S8: nested var + arithmetic ==="}
local P8 R8 in
   P8 = {GraphGeneration "fun g x = var a = x * x in var b = a + 10 in b / 2\ng 4"}
   R8 = {Evaluate P8}
   {System.showInfo "Result: "#R8#" (Expected: ((4*4)+10)/2 = (16+10)/2 = 13)"}
end

{System.showInfo "\n=== TEST S9: deeply nested var + parentheses ==="}
local P9 R9 in
   P9 = {GraphGeneration "fun h x = var a = (x + 1) in var b = (a * 2) in var c = (b - 3) in c + a\nh 5"}
   R9 = {Evaluate P9}
   {System.showInfo "Result: "#R9#" (Expected: a=6, b=12, c=9 → 9+6=15)"}
end

{System.showInfo "\n=== TEST S10: Underapplication of + → WHNF ==="}
local P10 R10 in
   P10 = prog(function:'f' args:[x]
               body:leaf(var:x)
               call:app(function:leaf(var:'+') arg:leaf(num:3)))
   R10 = {Evaluate P10}
   {System.showInfo "Result: "#{Value.toVirtualString R10 0 0}#" (Expected: WHNF/stuck)"}
end

{System.showInfo "\n=== TEST S11: Overapplication: f x y = x+y; call f 5 6 7 ==="}
local P11 R11 in
   P11 = {GraphGeneration "fun f x y = x + y\nf 5 6 7"}
   R11 = {Evaluate P11}
   {System.showInfo "Result: "#{Value.toVirtualString R11 0 0}#" (Expected: stuck - overapplication)"}
end

{System.showInfo "\n=== TEST S14: inside var binding division by zero ==="}
local P14 R14 in
   P14 = {GraphGeneration "fun f x = var y = 10 / 0 in y + 3\nf 0"}
   try
      R14 = {Evaluate P14}
      {System.showInfo "Result: "#{Value.toVirtualString R14 0 0}#" (Expected: Error division-by-zero)"}
   catch E then
      {System.showInfo "Error caught: "#{Value.toVirtualString E 0 0}#" (Expected: Error)"}
   end
end

{System.showInfo "\n=== TEST S15: fun fourtimes x = var y = x*x in y+y ==="}
local P15 R15 in
   P15 = {GraphGeneration "fun fourtimes x = var y = x*x in y+y\nfourtimes 2"}
   R15 = {Evaluate P15}
   {System.showInfo "Result: "#R15#" (Expected: 8)"}
end

{System.showInfo "\n=== TEST S19: return internal var without reducing ==="}
local P19 R19 in
   P19 = {GraphGeneration "fun t x = var y = x + 1 in y\nt 10"}
   R19 = {Evaluate P19}
   {System.showInfo "Result: "#R19#" (Expected: 11)"}
end

{System.showInfo "\n=== TEST S20: (((((3)))) + (((((4)))))) = 7 ==="}
local P20 R20 in
   P20 = {GraphGeneration "fun f x = (((((3)))) + (((((4))))))\nf 0"}
   R20 = {Evaluate P20}
   {System.showInfo "Result: "#R20#" (Expected: 7)"}
end

{System.showInfo "\n=== TEST S21: ((((x)))) ==="}
local P21 R21 in
   P21 = {GraphGeneration "fun f x = (((x)))\nf 9"}
   R21 = {Evaluate P21}
   {System.showInfo "Result: "#R21#" (Expected: 9)"}
end

{System.showInfo "\n=== TEST S22: fun square x = x * x * x ==="}
local P22 R22 in
   P22 = {GraphGeneration "fun square x = x * x * x\nsquare 3"}
   R22 = {Evaluate P22}
   {System.showInfo "Result: "#R22#" (Expected: 27)"}
end

{System.showInfo "\n=== TEST S23: duplicated arguments (x used twice) EXPECTED: 20 ==="}
local P23 R23 in
   P23 = {GraphGeneration "fun dup x y = x + x + y\ndup 5 10"}
   R23 = {Evaluate P23}
   {System.showInfo "Result: "#R23#" (Expected: 20)"}
end

{System.showInfo "\n=== TEST S24: shadowing — var x shadows function parameter x EXPECTED: 20 ==="}
local P24 R24 in
   P24 = {GraphGeneration "fun f x = var x = 10 in x + x\nf 3"}
   R24 = {Evaluate P24}
   {System.showInfo "Result: "#R24#" (Expected: 20)"}
end

{System.showInfo "\n=== TEST S25: chained var dependencies (a→b→c) EXPECTED: 12 ==="}
local P25 R25 in
   P25 = {GraphGeneration "fun chain x = var a = x + 1 in var b = a * 2 in var c = b - a in c + b\nchain 3"}
   R25 = {Evaluate P25}
   {System.showInfo "Result: "#R25#" (Expected: 12)"}
end

{System.showInfo "\n=== TEST F1: square (square 3) = 81 ==="}
local P26 R26 in
   P26 = {GraphGeneration "fun square x = x * x\nsquare (square 3)"}
   R26 = {Evaluate P26}
   {System.showInfo "Result: "#R26#" (Expected: 81)"}
end

{System.showInfo "\n=== TEST F2: nested sum_n calls ==="}
local P27 R27 in
   P27 = {GraphGeneration "fun sum_n x y z n = (x + y + z) * n\nsum_n 1 (sum_n 1 1 1 2) 3 2"}
   R27 = {Evaluate P27}
   {System.showInfo "Result: "#R27#" (Expected: (1+1+1)*2 = 6, then (1+6+3)*2 = 20)"}
end

{System.showInfo "\n=== TEST F3: nested arithmetic calls ==="}
local P28 R28 in
   P28 = {GraphGeneration "fun arithmetic x y = ((x + y) / (x - y)) * 2\narithmetic (arithmetic 5 6) (arithmetic 2 11)"}
   R28 = {Evaluate P28}
   {System.showInfo "Result: "#R28#" (Expected: arithmetic(5,6) = -22, arithmetic(2,11) = -2, then arithmetic(-22,-2) = 2)"}
end

{System.showInfo "\n=== TEST F4: var_use var_use 16 ==="}
local P29 R29 in
   P29 = {GraphGeneration "fun var_use x = var y = x + 1 in var z = y * 2 in z - 3\nvar_use (var_use 16)"}
   R29 = {Evaluate P29}
   {System.showInfo "Result: "#R29#" (Expected: var_use(16) = (16+1)*2-3 = 31, then var_use(31) = (31+1)*2-3 = 61)"}
end

{System.showInfo "\n=== TEST F5: fully parenthesized nested calls ==="}
local P30 R30 ResultVS30 TypeVS30 in
   P30 = {GraphGeneration "fun square x = x * x\n(square (square (square 2)))"}
   R30 = {Evaluate P30}
   ResultVS30 = {Value.toVirtualString R30 0 0}
   TypeVS30   = {Atom.toString {Value.type R30}}
   {System.showInfo "F5 Debug -> type: "#TypeVS30#", value: "#ResultVS30}
   {System.showInfo "Result: "#ResultVS30#" (Expected: square(square(square(2))) = square(square(4)) = square(16) = 256)"}
end

{System.showInfo "\n=== TEST F6: deep nested self-calls ==="}
local P31 R31 ResultVS31 TypeVS31 in
   P31 = {GraphGeneration "fun inc x = x + 1\ninc (inc (inc (inc 5)))"}
   R31 = {Evaluate P31}
   ResultVS31 = {Value.toVirtualString R31 0 0}
   TypeVS31   = {Atom.toString {Value.type R31}}
   {System.showInfo "F6 Debug -> type: "#TypeVS31#", value: "#ResultVS31}
   {System.showInfo "Result: "#ResultVS31#" (Expected: 5+1+1+1+1 = 9)"}
end

{System.showInfo "\n=== TEST F7: mixed nested calls ==="}
local P32 R32 ResultVS32 TypeVS32 in
   P32 = {GraphGeneration "fun f x = x * 2\nf (f 3) (f 4)"}
   R32 = {Evaluate P32}
   ResultVS32 = {Value.toVirtualString R32 0 0}
   TypeVS32   = {Atom.toString {Value.type R32}}
   {System.showInfo "F7 Debug -> type: "#TypeVS32#", value: "#ResultVS32}
   {System.showInfo "Result: "#ResultVS32#" (Expected: stuck - overapplication, f only takes 1 arg)"}
end

{System.showInfo "\n=== TEST F8: simulated composition f(g(h x)) ==="}
local P33 R33 ResultVS33 TypeVS33 in
   P33 = {GraphGeneration "fun comp x = ( (x+1) * 2 ) * 3\ncomp 5"}
   R33 = {Evaluate P33}
   ResultVS33 = {Value.toVirtualString R33 0 0}
   TypeVS33   = {Atom.toString {Value.type R33}}
   {System.showInfo "F8 Debug -> type: "#TypeVS33#", value: "#ResultVS33}
   {System.showInfo "Result: "#ResultVS33#" (Expected: (6 * 2)*3 = 36)"}
end

{System.showInfo "\n=== TEST F9: nested call inside var binding ==="}
local P34 R34 ResultVS34 TypeVS34 in
   P34 = {GraphGeneration "fun f x = var y = x * x in (y + y) + f 1\nf 1"}
   try
      R34 = {Evaluate P34}
      ResultVS34 = {Value.toVirtualString R34 0 0}
      TypeVS34   = {Atom.toString {Value.type R34}}
      {System.showInfo "F9 Debug -> type: "#TypeVS34#", value: "#ResultVS34}
      {System.showInfo "Result: "#ResultVS34#" (Expected: infinite recursion or stuck)"}
   catch E then
      {System.showInfo "Error caught: "#{Value.toVirtualString E 0 0}}
   end
end

{System.showInfo "\n=== TEST F10: nested calls + shadowing ==="}
local P35 R35 ResultVS35 TypeVS35 in
   P35 = {GraphGeneration "fun sh x = var x = x + 1 in sh x\nsh 1"}
   try
      R35 = {Evaluate P35}
      ResultVS35 = {Value.toVirtualString R35 0 0}
      TypeVS35   = {Atom.toString {Value.type R35}}
      {System.showInfo "F10 Debug -> type: "#TypeVS35#", value: "#ResultVS35}
      {System.showInfo "Result: "#ResultVS35#" (Expected: infinite loop or stuck)"}
   catch E then
      {System.showInfo "Error caught: "#{Value.toVirtualString E 0 0}}
   end
end

{System.showInfo "\n=== All tests completed ==="}

