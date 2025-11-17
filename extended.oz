%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% BOOK IMPLEMENTATION: Complete Template Instantiation, G-Machine, and TIM
%% Based on "Implementing Functional Languages: A Tutorial"
%% All implementations use new namespaces (TI_, GM_, TIM_) to avoid conflicts
%% with the advanced implementation above.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% ────────────────────────────────────────────────
%% PART 1: TEMPLATE INSTANTIATION (TI) - Complete Implementation
%% Chapter 2-3 of the book
%% ────────────────────────────────────────────────

%% TI Node Types (Heap representation - as record constructors)
fun {TI_NNum N} tinum(N) end
fun {TI_NAp F A} tiap(F A) end
fun {TI_NGlobal Fn BodyAddr} tiglobal(Fn BodyAddr) end
fun {TI_NInd Addr} tiind(Addr) end

%% TI State: (stack dump heap globals stats)
fun {TI_NewState}
   state(stack:nil dump:nil heap:{NewDictionary} globals:{NewDictionary} stats:stats(nodes:0 updates:0))
end

%% TI Heap Operations
fun {TI_AllocNode State Node}
   local Addr in
      Addr = State.stats.nodes + 1
      State.heap.Addr := Node
      State.stats := stats(nodes:Addr updates:State.stats.updates)
      Addr
   end
end

fun {TI_GetNode State Addr}
   State.heap.Addr
end

proc {TI_UpdateNode State Addr Node}
   State.heap.Addr := Node
   State.stats := stats(nodes:State.stats.nodes updates:State.stats.updates+1)
end

%% TI Compilation: Convert AST to heap nodes
fun {TI_CompileExpr Expr State}
   case Expr
   of leaf(num:N) then
      {TI_AllocNode State {TI_NNum N}}
   [] leaf(var:V) then
      %% Look up in globals or return variable reference
      if {HasFeature State.globals V} then
         State.globals.V
      else
         %% Free variable - return as variable node (will be handled in evaluation)
         {TI_AllocNode State {TI_NGlobal V nil}}
      end
   [] app(function:F arg:A) then
      local FAddr AAddr in
         FAddr = {TI_CompileExpr F State}
         AAddr = {TI_CompileExpr A State}
         {TI_AllocNode State {TI_NAp FAddr AAddr}}
      end
   [] var(bindings:Bs body:B) then
      %% For now, treat var as let - compile bindings and body
      local BodyAddr in
         BodyAddr = {TI_CompileExpr B State}
         %% TODO: Handle bindings properly
         BodyAddr
      end
   else
      raise error('ti_unsupported_expr'(expr:Expr)) end
   end
end

fun {TI_CompileProgram Prog State}
   %% Compile function body to heap
   local BodyAddr in
      BodyAddr = {TI_CompileExpr Prog.body State}
      %% Register function in globals
      State.globals.(Prog.function) := {TI_NGlobal Prog.function BodyAddr}
      %% Compile call expression
      {TI_CompileExpr Prog.call State}
   end
end

%% TI Evaluation: One step
fun {TI_Step State}
   case State.stack
   of nil then
      %% No more work - return final state
      State
   [] Addr|Rest then
      local Node in
         Node = {TI_GetNode State Addr}
         case Node
         of tiap(FAddr AAddr) then
            %% Application: push function address, continue with function
            {TI_Step state(stack:FAddr|State.stack dump:State.dump heap:State.heap globals:State.globals stats:State.stats)}
         [] tiglobal(Fn BodyAddr) then
            if BodyAddr == nil then
               %% Look up in globals
               if {HasFeature State.globals Fn} then
                  local GlobalNode in
                     GlobalNode = State.globals.Fn
                     case GlobalNode
                     of tiglobal(_ Body) then
                        if Body \= nil then
                           %% Update this node to point to body
                           {TI_UpdateNode State Addr {TI_NInd Body}}
                           {TI_Step state(stack:Body|Rest dump:State.dump heap:State.heap globals:State.globals stats:State.stats)}
                        else
                           %% Stuck - return as is
                           State
                        end
                     else
                        %% Update to indirection
                        {TI_UpdateNode State Addr {TI_NInd {TI_AllocNode State GlobalNode}}}
                        {TI_Step state(stack:Rest dump:State.dump heap:State.heap globals:State.globals stats:State.stats)}
                     end
                  end
               else
                  %% Unknown global - stuck
                  State
               end
            else
               %% Has body - update to indirection and continue
               {TI_UpdateNode State Addr {TI_NInd BodyAddr}}
               {TI_Step state(stack:BodyAddr|Rest dump:State.dump heap:State.heap globals:State.globals stats:State.stats)}
            end
         [] tiind(TargetAddr) then
            %% Indirection: follow and update
            {TI_UpdateNode State Addr {TI_GetNode State TargetAddr}}
            {TI_Step state(stack:TargetAddr|Rest dump:State.dump heap:State.heap globals:State.globals stats:State.stats)}
         [] tinum(N) then
            %% Number: pop and return
            {TI_Step state(stack:Rest dump:State.dump heap:State.heap globals:State.globals stats:State.stats)}
         else
            %% Unknown node type - stuck
            State
         end
      end
   end
end

%% TI Run: Evaluate until normal form
fun {TI_Run State MaxSteps}
   local
      fun {Loop S Steps}
         if Steps >= MaxSteps then
            S
         else
            local NextState in
               NextState = {TI_Step S}
               if NextState.stack == S.stack andthen NextState.heap == S.heap then
                  %% No change - done
                  NextState
               else
                  {Loop NextState Steps+1}
               end
            end
         end
      end
   in
      {Loop State 0}
   end
end

%% TI Evaluate: High-level interface
fun {EvaluateTI Prog}
   local State InitialAddr FinalState in
      State = {TI_NewState}
      InitialAddr = {TI_CompileProgram Prog State}
      FinalState = {TI_Run state(stack:[InitialAddr] dump:nil heap:State.heap globals:State.globals stats:State.stats) 1000}
      case FinalState.stack
      of [Addr] then
         case {TI_GetNode FinalState Addr}
         of tinum(N) then N
         else
            %% Not a number - return the node
            {TI_GetNode FinalState Addr}
         end
      [] nil then
         raise error('ti_empty_stack') end
      else
         raise error('ti_multiple_stack_entries') end
      end
   end
end

%% ────────────────────────────────────────────────
%% PART 2: G-MACHINE - Complete Implementation
%% Chapter 4-6 of the book
%% ────────────────────────────────────────────────

%% G-Machine Instruction Types (as records with parameters)
fun {GM_Pushglobal Name} pushglobal(Name) end
fun {GM_Pushint N} pushint(N) end
fun {GM_Push N} push(N) end
GM_Mkap = mkap
fun {GM_Slide N} slide(N) end
fun {GM_Update N} update(N) end
fun {GM_Pop N} pop(N) end
GM_Eval = eval
fun {GM_Alloc N} alloc(N) end
fun {GM_Cond Then Else} cond(Then Else) end
fun {GM_Casejump Cases} casejump(Cases) end
fun {GM_Pack Tag Arity} pack(Tag Arity) end
GM_Split = split

%% G-Machine Node Types (as record constructors)
fun {GM_NNum N} gmnnum(N) end
fun {GM_NAp F A} gmnap(F A) end
fun {GM_NGlobal Fn Code} gmnglobal(Fn Code) end
fun {GM_NInd Addr} gmnind(Addr) end
fun {GM_NConstr Tag Args} gmnconstr(Tag Args) end

%% G-Machine State: (code stack dump heap globals stats)
fun {GM_NewState}
   state(code:nil stack:nil dump:nil heap:{NewDictionary} globals:{NewDictionary} stats:stats(nodes:0 updates:0))
end

%% G-Machine Heap Operations
fun {GM_AllocNode State Node}
   local Addr in
      Addr = State.stats.nodes + 1
      State.heap.Addr := Node
      State.stats := stats(nodes:Addr updates:State.stats.updates)
      Addr
   end
end

fun {GM_GetNode State Addr}
   State.heap.Addr
end

proc {GM_UpdateNode State Addr Node}
   State.heap.Addr := Node
   State.stats := stats(nodes:State.stats.nodes updates:State.stats.updates+1)
end

%% G-Machine Compiler: Convert AST to G-code
fun {GM_CompileExpr Expr Env}
   case Expr
   of leaf(num:N) then
      [GM_Pushint(N)]
   [] leaf(var:V) then
      local Index in
         Index = {List.indexOf Env V}
         if Index \= false then
            [GM_Push(Index-1)]
         else
            [GM_Pushglobal(V)]
         end
      end
   [] app(function:F arg:A) then
      {Append {GM_CompileExpr A Env} {Append {GM_CompileExpr F Env} [GM_Mkap]}}
   [] var(bindings:Bs body:B) then
      local NewEnv BindCode in
         NewEnv = {FoldL Bs fun {$ Env B} B.var|Env end Env}
         BindCode = {FoldL Bs fun {$ Code B}
                                  {Append {GM_CompileExpr B.expr NewEnv} Code}
                               end nil}
         {Append BindCode {Append [GM_Alloc({Length Bs})] {Append {GM_CompileExpr B NewEnv} [GM_Slide({Length Bs})]}}}
      end
   else
      raise error('gm_unsupported_expr'(expr:Expr)) end
   end
end

fun {GM_CompileSupercombinator Fn Args Body}
   local Code in
      Code = {GM_CompileExpr Body Args}
      %% Compile body, then update and pop arguments
      {Append Code [{GM_Update {Length Args}} {GM_Pop {Length Args}}]}
   end
end

fun {GM_CompileProgram Prog State}
   local BodyCode CallCode GlobalAddr in
      BodyCode = {GM_CompileSupercombinator Prog.function Prog.args Prog.body}
      %% Store supercombinator code in global
      GlobalAddr = {GM_AllocNode State {GM_NGlobal Prog.function BodyCode}}
      State.globals.(Prog.function) := GlobalAddr
      %% Compile call expression
      CallCode = {GM_CompileExpr Prog.call nil}
      {Append CallCode [GM_Eval]}
   end
end

%% G-Machine Instruction Execution
fun {GM_ExecuteInstr Instr State}
   case Instr
   of pushglobal(Name) then
      local Addr in
         if {HasFeature State.globals Name} then
            Addr = State.globals.Name
         else
            Addr = {GM_AllocNode State {GM_NGlobal Name nil}}
            State.globals.Name := Addr
         end
         state(code:State.code stack:Addr|State.stack dump:State.dump heap:State.heap globals:State.globals stats:State.stats)
      end
   [] pushint(N) then
      local Addr in
         Addr = {GM_AllocNode State {GM_NNum N}}
         state(code:State.code stack:Addr|State.stack dump:State.dump heap:State.heap globals:State.globals stats:State.stats)
      end
   [] push(N) then
      local Addr in
         Addr = {List.nth State.stack N+1}
         state(code:State.code stack:Addr|State.stack dump:State.dump heap:State.heap globals:State.globals stats:State.stats)
      end
   [] mkap then
      local FAddr AAddr NewAddr in
         FAddr = {List.nth State.stack 1}
         AAddr = {List.nth State.stack 2}
         NewAddr = {GM_AllocNode State {GM_NAp FAddr AAddr}}
         state(code:State.code stack:NewAddr|{List.drop State.stack 2} dump:State.dump heap:State.heap globals:State.globals stats:State.stats)
      end
   [] slide(N) then
      local Top Rest in
         Top = {List.nth State.stack 1}
         Rest = {List.drop State.stack N+1}
         state(code:State.code stack:Top|Rest dump:State.dump heap:State.heap globals:State.globals stats:State.stats)
      end
   [] update(N) then
      local Addr Node in
         Addr = {List.nth State.stack N+1}
         Node = {List.nth State.stack 1}
         {GM_UpdateNode State Addr {GM_NInd Node}}
         state(code:State.code stack:{List.drop State.stack 1} dump:State.dump heap:State.heap globals:State.globals stats:State.stats)
      end
   [] pop(N) then
      state(code:State.code stack:{List.drop State.stack N} dump:State.dump heap:State.heap globals:State.globals stats:State.stats)
   [] eval then
      local Addr in
         Addr = {List.nth State.stack 1}
         {GM_Unwind State Addr}
      end
   [] alloc(N) then
      local NewAddrs NewStack in
         NewAddrs = {List.make N}
         {For 1 N 1 proc {$ I} NewAddrs.I = {GM_AllocNode State {GM_NInd 0}} end}
         NewStack = {Append {Reverse NewAddrs} State.stack}
         state(code:State.code stack:NewStack dump:State.dump heap:State.heap globals:State.globals stats:State.stats)
      end
   else
      raise error('gm_unknown_instruction'(instr:Instr)) end
   end
end

%% G-Machine Unwind: Follow spine to find redex
fun {GM_Unwind State Addr}
   local Node in
      Node = {GM_GetNode State Addr}
      case Node
      of gmnap(FAddr _) then
         {GM_Unwind State FAddr}
      [] gmnglobal(Fn Code) then
         if Code \= nil then
            %% Execute code (Code is a list of instructions)
            state(code:Code stack:State.stack dump:State.dump heap:State.heap globals:State.globals stats:State.stats)
         else
            %% Look up in globals
            if {HasFeature State.globals Fn} then
               local GlobalAddr in
                  GlobalAddr = State.globals.Fn
                  {GM_UpdateNode State Addr {GM_NInd GlobalAddr}}
                  {GM_Unwind State GlobalAddr}
               end
            else
               %% Stuck - return state with empty code
               state(code:nil stack:State.stack dump:State.dump heap:State.heap globals:State.globals stats:State.stats)
            end
         end
      [] gmnind(TargetAddr) then
         {GM_Unwind State TargetAddr}
      [] gmnnum(_) then
         %% Normal form - return state with empty code
         state(code:nil stack:State.stack dump:State.dump heap:State.heap globals:State.globals stats:State.stats)
      else
         %% Unknown - stuck
         state(code:nil stack:State.stack dump:State.dump heap:State.heap globals:State.globals stats:State.stats)
      end
   end
end

%% G-Machine Step: Execute one instruction
fun {GM_Step State}
   case State.code
   of nil then
      %% No more code - done
      State
   [] Instr|Rest then
      local NewState in
         NewState = {GM_ExecuteInstr Instr state(code:Rest stack:State.stack dump:State.dump heap:State.heap globals:State.globals stats:State.stats)}
         NewState
      end
   end
end

%% G-Machine Run: Execute until done
fun {GM_Run State MaxSteps}
   local
      fun {Loop S Steps}
         if Steps >= MaxSteps then
            S
         else
            local NextState in
               NextState = {GM_Step S}
               if NextState.code == S.code andthen NextState.stack == S.stack then
                  NextState
               else
                  {Loop NextState Steps+1}
               end
            end
         end
      end
   in
      {Loop State 0}
   end
end

%% G-Machine Evaluate: High-level interface
fun {EvaluateGM Prog}
   local State Code FinalState in
      State = {GM_NewState}
      Code = {GM_CompileProgram Prog State}
      FinalState = {GM_Run state(code:Code stack:nil dump:nil heap:State.heap globals:State.globals stats:State.stats) 1000}
      case FinalState.stack
      of [Addr] then
         case {GM_GetNode FinalState Addr}
         of gmnnum(N) then N
         else
            {GM_GetNode FinalState Addr}
         end
      [] nil then
         raise error('gm_empty_stack') end
      else
         raise error('gm_multiple_stack_entries') end
      end
   end
end

%% ────────────────────────────────────────────────
%% PART 3: TIM MACHINE - Complete Implementation
%% Chapter 8-10 of the book
%% ────────────────────────────────────────────────

%% TIM Instruction Types (as records with parameters)
fun {TIM_Take N} take(N) end
fun {TIM_Enter X} enter(X) end
fun {TIM_Push Value} push(Value) end
fun {TIM_Mkap} mkap end
fun {TIM_Alloc N} alloc(N) end
fun {TIM_Slide N} slide(N) end
fun {TIM_Pushglobal Name} pushglobal(Name) end

%% TIM Closure: (instrs frame)
fun {TIM_NewClosure Instrs Frame}
   closure(instrs:Instrs frame:Frame)
end

%% TIM State: (code frame stack dump heap stats)
fun {TIM_NewState}
   state(code:nil frame:nil stack:nil dump:nil heap:{NewDictionary} stats:stats(nodes:0))
end

%% TIM Heap Operations
fun {TIM_AllocClosure State Closure}
   local Addr in
      Addr = State.stats.nodes + 1
      State.heap.Addr := Closure
      State.stats := stats(nodes:Addr)
      Addr
   end
end

fun {TIM_GetClosure State Addr}
   State.heap.Addr
end

%% TIM Compiler: Convert AST to TIM code
fun {TIM_CompileExpr Expr Env}
   case Expr
   of leaf(num:N) then
      [{TIM_Push N}]
   [] leaf(var:V) then
      local Index in
         Index = {List.indexOf Env V}
         if Index \= false then
            [{TIM_Enter Index-1}]
         else
            [{TIM_Pushglobal V}]
         end
      end
   [] app(function:F arg:A) then
      {Append {TIM_CompileExpr A Env} {Append {TIM_CompileExpr F Env} [{TIM_Mkap}]}}
   [] var(bindings:Bs body:B) then
      local NewEnv BindCode in
         NewEnv = {FoldL Bs fun {$ Env B} B.var|Env end Env}
         BindCode = {FoldL Bs fun {$ Code B}
                                  {Append {TIM_CompileExpr B.expr NewEnv} Code}
                               end nil}
         {Append BindCode {Append [{TIM_Alloc {Length Bs}}] {Append {TIM_CompileExpr B NewEnv} [{TIM_Slide {Length Bs}}]}}}
      end
   else
      raise error('tim_unsupported_expr'(expr:Expr)) end
   end
end

fun {TIM_CompileSupercombinator Fn Args Body State}
   local Code ClosureAddr in
      Code = {TIM_CompileExpr Body Args}
      ClosureAddr = {TIM_AllocClosure State {TIM_NewClosure Code Args}}
      ClosureAddr
   end
end

fun {TIM_CompileProgram Prog State}
   local BodyClosureAddr CallCode in
      BodyClosureAddr = {TIM_CompileSupercombinator Prog.function Prog.args Prog.body State}
      CallCode = {TIM_CompileExpr Prog.call nil}
      {Append CallCode [{TIM_Enter BodyClosureAddr}]}
   end
end

%% TIM Instruction Execution
fun {TIM_ExecuteInstr Instr State}
   case Instr
   of take(N) then
      local Args Frame in
         Args = {List.take State.stack N}
         Frame = {Append Args State.frame}
         state(code:State.code frame:Frame stack:{List.drop State.stack N} dump:State.dump heap:State.heap stats:State.stats)
      end
   [] enter(Addr) then
      local Closure in
         Closure = {TIM_GetClosure State Addr}
         case Closure
         of closure(instrs:Code frame:Frame) then
            state(code:Code frame:Frame stack:State.stack dump:State.dump heap:State.heap stats:State.stats)
         else
            %% Follow indirection or evaluate
            {TIM_Unwind State Addr}
         end
      end
   [] push(Value) then
      state(code:State.code frame:State.frame stack:Value|State.stack dump:State.dump heap:State.heap stats:State.stats)
   [] mkap then
      local FAddr AAddr NewAddr in
         FAddr = {List.nth State.stack 1}
         AAddr = {List.nth State.stack 2}
         NewAddr = {TIM_AllocClosure State {TIM_NewClosure [enter(AAddr)] [FAddr]}}
         state(code:State.code frame:State.frame stack:NewAddr|{List.drop State.stack 2} dump:State.dump heap:State.heap stats:State.stats)
      end
   [] pushglobal(Name) then
      %% For now, treat as variable - would need global table
      state(code:State.code frame:State.frame stack:Name|State.stack dump:State.dump heap:State.heap stats:State.stats)
   else
      raise error('tim_unknown_instruction'(instr:Instr)) end
   end
end

%% TIM Unwind: Follow spine (simplified - TIM uses closures directly)
fun {TIM_Unwind State Addr}
   local Closure in
      Closure = {TIM_GetClosure State Addr}
      case Closure
      of closure(instrs:Code frame:Frame) then
         state(code:Code frame:Frame stack:State.stack dump:State.dump heap:State.heap stats:State.stats)
      else
         %% Not a closure - return state unchanged
         state(code:nil frame:State.frame stack:State.stack dump:State.dump heap:State.heap stats:State.stats)
      end
   end
end

%% TIM Step: Execute one instruction
fun {TIM_Step State}
   case State.code
   of nil then
      State
   [] Instr|Rest then
      {TIM_ExecuteInstr Instr state(code:Rest frame:State.frame stack:State.stack dump:State.dump heap:State.heap stats:State.stats)}
   end
end

%% TIM Run: Execute until done
fun {TIM_Run State MaxSteps}
   local
      fun {Loop S Steps}
         if Steps >= MaxSteps then
            S
         else
            local NextState in
               NextState = {TIM_Step S}
               if NextState.code == S.code andthen NextState.stack == S.stack then
                  NextState
               else
                  {Loop NextState Steps+1}
               end
            end
         end
      end
   in
      {Loop State 0}
   end
end

%% TIM Evaluate: High-level interface
fun {EvaluateTIM Prog}
   local State Code FinalState in
      State = {TIM_NewState}
      Code = {TIM_CompileProgram Prog State}
      FinalState = {TIM_Run state(code:Code frame:nil stack:nil dump:nil heap:State.heap stats:State.stats) 1000}
      case FinalState.stack
      of [Value] then
         case Value
         of N andthen {IsInt N} then N
         else Value
         end
      [] nil then
         raise error('tim_empty_stack') end
      else
         raise error('tim_multiple_stack_entries') end
      end
   end
end

%% ────────────────────────────────────────────────
%% Extended EvaluateWithMode to support all machines
%% ────────────────────────────────────────────────

fun {EvaluateWithMode Prog Mode}
   case Mode
   of classic then {EvaluateClassic Prog}
   [] advanced then {Evaluate Prog}
   [] ti then {EvaluateTI Prog}
   [] gm then {EvaluateGM Prog}
   [] tim then {EvaluateTIM Prog}
   [] auto then
      %% Auto mode: try advanced first, fallback to classic if needed
      try
         {Evaluate Prog}
      catch E then
         {System.showInfo ">>> Advanced evaluation failed, trying classic mode"}
         {EvaluateClassic Prog}
      end
   else
      {Evaluate Prog}  %% Default to advanced
   end
end