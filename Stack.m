(* ::Package:: *)

BeginPackage["Stack`"];
push::usage="push[s,e] pushes e into stack s.";
pop::usage="pop[s] pops the top of stack s.";
top::usage="top[s] returns the top of stack s.";
EmptyStackQ::usage="EmptyStackQ[s] returns True if stack s is empty and False otherwise.";

Begin["`Private`"];

EmptyStackQ[stack_] := Length[stack]==0&&ListQ[stack]

SetAttributes[push,HoldFirst]
push[stack_,elem_] := (stack = {elem,stack};);

SetAttributes[pop,HoldFirst]
pop[stack_]:=
	If[!EmptyStackQ[stack],
	 With[{elem=First[stack]},
				stack=Last[stack];elem]];

top[{}]:=Null
top[stack_] := First[stack]
SetAttributes[{push,pop,top,EmptyStackQ},ReadProtected];


(*Adapted from:\[LineSeparator]http://library.wolfram.com/infocenter/Conferences/388/*)
	
End[];
EndPackage[];
