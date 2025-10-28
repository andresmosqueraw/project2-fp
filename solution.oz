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