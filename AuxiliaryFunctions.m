(* ::Package:: *)

BeginPackage["AuxiliaryFunctions`",{"Formulas`","StateTuple`"}];
\[Sigma]plus::usage="Auxiliary function \[Sigma]plus[t,I,Q] return the set of formulas free from the next operator.";
\[Sigma]minus::usage="Auxiliary function \[Sigma]minus[t,I,Q] return the set of formulas free from the next operator.";
\[Eta]plus::usage="\[Eta]plus[i,j,Q] returns the set of formulas that must hold for agent j, forced by the interaction with agent i.";
\[Eta]minus::usage="\[Eta]minus[i,j,Q] returns the set of formulas that cannot hold for agent j, if agent j synchronized with i.";
\[Eta]bowtie::usage="\[Eta]bowtie[i,j,Q] returns the set of formulas that force the synchronization between agents i and j.";
\[Eta]\[NumberSign]::usage="\[Eta]\[NumberSign][i,j,Q] returns the set of formulas that present a possible synchronization between agents i and j.";


Begin["`Private`"];


SetAttributes[{\[Sigma]plus,\[Sigma]minus,\[Eta]plus,\[Eta]minus,\[Eta]bowtie,\[Eta]\[NumberSign]},ReadProtected];


\[Sigma]plus=Function[{t,I,Q},
	Module[{Q1,l={},xx},
		Copy[Q,Q1];
		While[STpos[Q1,"Next",True]!=0,
			xx=STSubParts[Q1,"Next",True];
			If[MemberQ[I,xx[[1]]],
				AppendTo[l,\!\(
\*SubscriptBox[\(@\), \(xx[\([1]\)]\)]\([xx[\([2]\)]]\)\)];
			];
		RemoveQplus[Q1,\!\(
\*SubscriptBox[\(@\), \(xx[\([1]\)]\)]\([X\ xx[\([2]\)]]\)\)]
		];
		l
	]
];


\[Sigma]minus=Function[{t,I,Q},
	Module[{Q1,l={},xx},
		Copy[Q,Q1];
		While[STpos[Q1,"Next",False]!=0,
			xx=STSubParts[Q1,"Next",False];
			If[MemberQ[I,xx[[1]]],
				AppendTo[l,\!\(
\*SubscriptBox[\(@\), \(xx[\([1]\)]\)]\([xx[\([2]\)]]\)\)];
			];
			RemoveQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(xx[\([1]\)]\)]\([X\ xx[\([2]\)]]\)\)]
		];
		l
	]
];


\[Eta]plus=Function[{i,j,Q},
	Module[{Q1,l={},cc},
		Copy[Q,Q1];
		While[STpos[Q1,"Communication",True]!=0,
			cc=STSubParts[Q1,"Communication",True];
			If[cc[[1]]==i&&cc[[2]]==j,
				AppendTo[l,\!\(
\*SubscriptBox[\(@\), \(j\)]\([cc[\([3]\)]]\)\)];
			];
			RemoveQplus[Q1,\!\(
\*SubscriptBox[\(@\), \(cc[\([1]\)]\)]\([
\(\*SubscriptBox[\(\[Copyright]\), \(cc[\([2]\)]\)]\)[cc[\([3]\)]]]\)\)];
		];
		l
	]
];


\[Eta]minus=Function[{i,j,Q},
	Module[{Q1,l={},cc},
		Copy[Q,Q1];
		While[STpos[Q1,"Communication",False]!=0,
			cc=STSubParts[Q1,"Communication",False];
			If[cc[[1]]==i&&cc[[2]]==j,
				AppendTo[l,\!\(
\*SubscriptBox[\(@\), \(j\)]\([cc[\([3]\)]]\)\)];
			];
			RemoveQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(cc[\([1]\)]\)]\([
\(\*SubscriptBox[\(\[Copyright]\), \(cc[\([2]\)]\)]\)[cc[\([3]\)]]]\)\)];
		];
		l
	]
];


\[Eta]bowtie=Function[{i,j,Q},
	Module[{Q1,l={},cc},
		Copy[Q,Q1];
		While[STpos[Q1,"Communication",True]!=0,
			cc=STSubParts[Q1,"Communication",True];
			If[cc[[1]]==i&&cc[[2]]==j,
				AppendTo[l,\!\(
\*SubscriptBox[\(@\), \(i\)]\([
\(\*SubscriptBox[\(\[Copyright]\), \(j\)]\)[cc[\([3]\)]]]\)\)];
			];
			RemoveQplus[Q1,\!\(
\*SubscriptBox[\(@\), \(cc[\([1]\)]\)]\([
\(\*SubscriptBox[\(\[Copyright]\), \(cc[\([2]\)]\)]\)[cc[\([3]\)]]]\)\)];
		];
		l
	]
];


\[Eta]\[NumberSign]=Function[{i,j,Q},
	Module[{Q1,l={},cc},
		Copy[Q,Q1];
		While[STpos[Q1,"Communication",False]!=0,
			cc=STSubParts[Q1,"Communication",False];
			If[cc[[1]]==i&&cc[[2]]==j,
				AppendTo[l,\!\(
\*SubscriptBox[\(@\), \(i\)]\([
\(\*SubscriptBox[\(\[Copyright]\), \(j\)]\)[cc[\([3]\)]]]\)\)];
			];
			RemoveQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(cc[\([1]\)]\)]\([
\(\*SubscriptBox[\(\[Copyright]\), \(cc[\([2]\)]\)]\)[cc[\([3]\)]]]\)\)]
		];
		l
	]
];

End[];
EndPackage[]
