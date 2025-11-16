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
            local A B Rest in
               A#B#Rest = {Pop2 Stk}
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
         local Y in
            Y = {List.filter Xs fun {$ T} T \= '(' andthen T \= ')' end}
            if Y \= nil andthen {IsOp {List.nth Y 1}} then
               {BuildLeft Y}
            else
               {BuildRight Y}
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

      FunBody   = {BuildExpr BodyTokens}
      CallGraph = {BuildExpr TokensCall}

      prog(function:FName args:ArgsTokens body:FunBody call:CallGraph)
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
    case Head
    of leaf(var:Op) then
       if {IsPrimitive Op} then 2
       elseif Op==Prog.function then {Length Prog.args}
       else 0
       end
    [] leaf(num:_) then 0
    else 0
    end
 end
 
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
 
 fun {Unwind Expr Args Apps}
    case Expr
    of app(function:F arg:A) then
       {Unwind F A|Args Expr|Apps}
    else
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
      var(bindings:Bs body:{Subst B Var WithNode})
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

fun {EvalVarBindings Bindings Body}
   case Bindings
   of nil then Body
   [] bind(var:V expr:E)|Rest then
      local EvaluatedE in
         EvaluatedE = {EvalToNum E prog(function:'temp' args:nil body:E call:E)}
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
   case Expr
   of leaf(num:N) then N
   [] leaf(var:_) then
      raise error('expected_number'(expr:Expr status:whnf)) end
   [] var(bindings:Bs body:B) then
      local EvaluatedBody in
         EvaluatedBody = {EvalVarBindings Bs B}
         {EvalToNum EvaluatedBody Prog}
      end
   [] app(function:_ arg:_) then
      local P R P2 in
         P  = prog(function:Prog.function args:Prog.args body:Prog.body call:Expr)
         R  = {NextReduction P}
         if R.status == ok then
            P2 = {Reduce P}
            if P2.call == P.call then
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
      raise error('unexpected_expr_in_evaltonum'(expr:Expr)) end
   end
end

fun {Reduce Prog}
   local R NewNode NewCall in
      R = {NextReduction Prog}
      if R.status \= ok then
         Prog
      else
         case R.kind
         of supercombinator(Fn) then
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
                  NewNode = {ApplyRest Instanced R.rest}
               end
            end            
         [] primitive(Op) then
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
                  NewNode = R.root
               end
            end         
         else
            NewNode = R.head
         end

         NewCall = {ReplaceSub Prog.call R.root NewNode}
         prog(function:Prog.function args:Prog.args body:Prog.body call:NewCall)
      end
   end
end


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Task 4
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fun {Evaluate Prog}
   case Prog.call
   of leaf(num:N) then N
   [] _ then
      local R Pnext in
         R = {NextReduction Prog}
         if R.status == ok then
            Pnext = {Reduce Prog}
            if Pnext.call == Prog.call then
               case Prog.call
               of leaf(num:N) then N
               [] _ then Prog.call
               end
            else
               {Evaluate Pnext}
            end         

         elseif R.status == whnf then
            local Normal in
               case Prog.call
               of var(bindings:Bs body:B) then
                  Normal = {EvalVarBindings Bs B}
               [] _ then
                  Normal = {EvaluateDeep Prog.call Prog}
               end
         
               if Normal == Prog.call then
                  Prog.call
               else
                  {Evaluate prog(function:Prog.function args:Prog.args body:Prog.body call:Normal)}
               end
            end 
         else
            case Prog.call
            of leaf(num:N) then N
            [] var(bindings:Bs body:B) then
               {Evaluate prog(function:Prog.function args:Prog.args body:Prog.body call:B)}
            [] _ then Prog.call
            end
         end
      end
   end
end

fun {EvaluateDeep Expr Prog}
   case Expr
   of leaf(num:N) then Expr
   [] leaf(var:_) then Expr
   [] app(function:F arg:A) then
      app(function:{EvaluateDeep F Prog} arg:{EvaluateDeep A Prog})
   [] var(bindings:Bs body:B) then
      {EvaluateDeep {EvalVarBindings Bs B} Prog}
   else
      Expr
   end
end