(* ::Package:: *)

BeginPackage["Rules`",{"Formulas`","StateTuple`","AuxiliaryFunctions`"}];

GlobalImplicationPlus::usage="GlobalImplicationPlus[Q,\[Alpha],\[Beta]] returns {Q1,Q2}, the two State Tuples resulting from applying the rule.
The usage of this function presupposes the existence of an implication \[Alpha]\[Implies]\[Beta] in Q+. ";
GlobalImplicationMinus::usage="GlobalImplicationMinus[Q,\[Alpha],\[Beta]] returns the State Tuple resulting from aplying the rule.
The usage of this function presupposes the existence of an implication \[Alpha]\[Implies]\[Beta] in Q-. ";

GlobalOrMinus::usage="GlobalOrMinus[Q,\[Alpha],\[Beta]] returns the State Tuple resulting from aplying the rule.
The usage of this function presupposes the existence of an disjunction \[Alpha]\[Or]\[Beta] in Q-. 
Recall that \[Phi]\[Or]\[Psi] is defined as an abbreviation of (\[Not]\[Phi])\[Implies]\[Psi].";
GlobalOrPlus::usage="GlobalOrPlus[Q,\[Alpha],\[Beta]] returns {Q1,Q2}, the two State Tuples resulting from applying the rule.
The usage of this function presupposes the existence of an disjunction \[Alpha]\[Or]\[Beta] in Q+. 
Recall that \[Phi]\[Or]\[Psi] is defined as an abbreviation of (\[Not]\[Phi])\[Implies]\[Psi].";

GlobalAndPlus::usage="GlobalAndPlus[Q,\[Alpha],\[Beta]] returns the State Tuple resulting from aplying the rule.
The usage of this function presupposes the existence of an conjunction \[Alpha]\[And]\[Beta] in Q+. 
Recall that \[Phi]\[And]\[Psi] is defined as an abbreviation of (\[Not](\[Phi]\[Implies](\[Not]\[Psi]))).";

GlobalAndMinus::usage="GlobalAndMinus[Q,\[Alpha],\[Beta]] returns {Q1,Q2}, the two State Tuples resulting from applying the rule.
The usage of this function presupposes the existence of an conjunction \[Alpha]\[And]\[Beta] in Q-. 
Recall that \[Phi]\[And]\[Psi] is defined as an abbreviation of (\[Not](\[Phi]\[Implies](\[Not]\[Psi]))).";

GlobalNotPlus::usage="GlobalNotPlus[Q,\[Phi]] returns the State Tuple resulting from aplying the rule.
The usage of this function presupposes the existence of [\[Not]\[Phi]] in Q+.
Recall that \[Not] is defined as an abbreviation of \[Phi]\[Implies]\[UpTee].";

GlobalNotMinus::usage="GlobalNotMinus[Q,\[Phi]] returns the State Tuple resulting from aplying the rule.
The usage of this function presupposes the existence of [\[Not]\[Phi]] in Q-.
Recall that \[Not] is defined as an abbreviation of \[Phi]\[Implies]\[UpTee].";

LocalImplicationPlus::usage="LocalImplicationPlus[Q,i,\[Phi],\[Psi]] returns {Q1,Q2}, the two State Tuples resulting from applying the rule.
The usage of this function presupposes the existence of an implication \!\(\*SubscriptBox[\(@\), \(i\)]\)[\[Phi]\[Implies]\[Psi]] in Q+.";
LocalImplicationMinus::usage="LocalImplicationMinus[Q,i,\[Phi],\[Psi]] returns the State Tuple resulting from aplying the rule.
The usage of this function presupposes the existence of an implication \!\(\*SubscriptBox[\(@\), \(i\)]\)[\[Phi]\[Implies]\[Psi]] in Q-. ";

GPlus::usage="GPlus[Q,i,\[Phi]] returns the State Tuple resulting from aplying the rule.
The usage of this function presupposes the existence of \!\(\*SubscriptBox[\(@\), \(i\)]\)[G \[Phi]] in Q+.";
GMinus::usage="GMinus[Q,i,\[Phi]] returns {Q1,Q2}, the two State Tuples resulting from applying the rule.
The usage of this function presupposes the existence of \!\(\*SubscriptBox[\(@\), \(i\)]\)[G \[Phi]] in Q+.";

\[Copyright]Plus::usage="\[Copyright]Plus[Q,i,j,\[Phi]] returns the State Tuple resulting from aplying the rule.
The usage of this function presupposes the existence of SubscriptBox[\(@\), \(i\)[SubscriptBox[\(\[Copyright]\), \(j\)[\[Phi]]] in Q+.";
\[Copyright]Minus::usage="\[Copyright]Plus[Q,i,j,\[Phi]] returns {Q1,Q2}, the two State Tuples resulting from applying the rule.
The usage of this function presupposes the existence of SubscriptBox[\(@\), \(i\)[SubscriptBox[\(\[Copyright]\), \(j\)[\[Phi]]] in Q-.";

XRule::usage="XRule[Q] returns a list of State Tuples resulting from aplying the rule and the subset K they are associated with.
The usage of this function presupposes that all the formulas have been decomposed except for those referring to the next state.";

FPlus::usage="FPlus[Q,i,\[Phi]] returns {Q1,Q2}, the two State Tuples resulting from applying the rule.
The usage of this function presupposes the existence of SubscriptBox[\(@\), \(i\)[F \[Phi]] in Q+.
Recall that F is defined as an abbreviation F\[Congruent]\[Not]G \[Not]\[Phi].";

FMinus::usage="FMinus[Q,i,\[Phi]] returns the State Tuple resulting from aplying the rule.
The usage of this function presupposes the existence of SubscriptBox[\(@\), \(i\)[F \[Phi]] in Q-.
Recall that F is defined as an abbreviation F\[Congruent]\[Not]G \[Not]\[Phi].";

OrPlus::usage="OrPlus[Q,i,\[Phi],\[Psi]] returns {Q1,Q2}, the two State Tuples resulting from applying the rule.
The usage of this function presupposes the existence of SubscriptBox[\(@\), \(i\)[\[Phi]\[Or]\[Psi]] in Q+.
Recall that \[Phi]\[Or]\[Psi] is defined as an abbreviation of (\[Not]\[Phi])\[Implies]\[Psi].";

OrMinus::usage="OrMinus[Q,i,\[Phi],\[Psi]] returns the State Tuple resulting from aplying the rule.
The usage of this function presupposes the existence of SubscriptBox[\(@\), \(i\)[\[Phi]\[Or]\[Psi]] in Q-.
Recall that \[Phi]\[Or]\[Psi] is defined as an abbreviation of (\[Not]\[Phi])\[Implies]\[Psi].";

AndPlus::usage="AndPlus[Q,i,\[Phi],\[Psi]] returns the State Tuple resulting from aplying the rule.
The usage of this function presupposes the existence of SubscriptBox[\(@\), \(i\)[\[Phi]\[And]\[Psi]] in Q+.
Recall that \[Phi]\[And]\[Psi] is defined as an abbreviation of (\[Not](\[Phi]\[Implies](\[Not]\[Psi]))).";

AndMinus::usage="AndMinus[Q,i,\[Phi],\[Psi]] returns {Q1,Q2}, the two State Tuples resulting from applying the rule.
The usage of this function presupposes the existence of SubscriptBox[\(@\), \(i\)[\[Phi]\[And]\[Psi]] in Q+.
Recall that \[Phi]\[And]\[Psi] is defined as an abbreviation of (\[Not](\[Phi]\[Implies](\[Not]\[Psi]))).";

NotPlus::usage="NotPlus[Q,i,\[Phi]] returns the State Tuple resulting from aplying the rule.
The usage of this function presupposes the existence of SubscriptBox[\(@\), \(i\)[\[Not]\[Phi]] in Q+.
Recall that \[Not] is defined as an abbreviation of \[Phi]\[Implies]\[UpTee].";
NotMinus::usage="NotMinus[Q,i,\[Phi]] returns the State Tuple resulting from aplying the rule.
The usage of this function presupposes the existence of SubscriptBox[\(@\), \(i\)[\[Not]\[Phi]] in Q-.
Recall that \[Not] is defined as an abbreviation of \[Phi]\[Implies]\[UpTee].";

UPlus::usage="UPlus[Q,i,\[Phi],\[Psi]] returns {Q1,Q2}, the two State Tuples resulting from applying the rule.
The usage of this function presupposes the existence of SubscriptBox[\(@\), \(i\)[\[Phi]\[ScriptCapitalU]\[Psi]] in Q+.";
UMinus::usage="UMinus[Q,i,\[Phi],\[Psi]] returns {Q1,Q2}, the two State Tuples resulting from applying the rule.
The usage of this function presupposes the existence of SubscriptBox[\(@\), \(i\)[\[Phi]\[ScriptCapitalU]\[Psi]] in Q-.";

LocalEquiPlus::usage="LocalEquiPlus[Q,i,\[Phi],\[Psi]] returns {Q1,Q2}, the two State Tuples resulting from applying the rule.
The usage of this function presupposes the existence of SubscriptBox[\(@\), \(i\)[\[Phi]\[Equivalent]\[Psi]] in Q+.";
LocalEquiMinus::usage="LocalEquiMinus[Q,i,\[Phi],\[Psi]] returns {Q1,Q2}, the two State Tuples resulting from applying the rule.
The usage of this function presupposes the existence of SubscriptBox[\(@\), \(i\)[\[Phi]\[Equivalent]\[Psi]] in Q-.";

GlobalEquiPlus::usage="GlobalEquiPlus[Q,i,\[Phi],\[Psi]] returns {Q1,Q2}, the two State Tuples resulting from applying the rule.
The usage of this function presupposes the existence of \[Alpha]\[Equivalent]\[Beta] in Q+.";
GlobalEquiMinus::usage="GlobalEquiMinus[Q,i,\[Phi],\[Psi]] returns {Q1,Q2}, the two State Tuples resulting from applying the rule.
The usage of this function presupposes the existence of \[Alpha]\[Equivalent]\[Beta] in Q-.";


SetAttributes[{GlobalImplicationPlus,GlobalImplicationMinus,GlobalOrMinus,GlobalOrPlus,
GlobalAndPlus,GlobalAndMinus,GlobalNotPlus,GlobalNotMinus,
LocalImplicationPlus,LocalImplicationMinus,
GPlus,GMinus,\[Copyright]Plus,\[Copyright]Minus,XRule,FPlus,FMinus,
OrPlus,OrMinus,AndPlus,AndMinus,NotPlus,
NotMinus,UPlus,UMinus,LocalEquiPlus,LocalEquiMinus,GlobalEquiPlus,
GlobalEquiMinus,auxf,L},ReadProtected];


Begin["`Private`"];

(*Global Rules*)
(*Global Implication Rules*)
GlobalImplicationPlus=Function[{Q,\[Alpha],\[Beta]},
(*It presupposes the existence of an implication \[Alpha]\[Implies]\[Beta] in Q+*)
	Module[{Q1,Q2},
		StateTuple`Copy[Q,Q1];
		StateTuple`Copy[Q,Q2];
		StateTuple`RemoveQplus[Q1,Implies[\[Alpha],\[Beta]]];
		StateTuple`InsertQminus[Q1,\[Alpha]];

		StateTuple`RemoveQplus[Q2,Implies[\[Alpha],\[Beta]]];
		StateTuple`InsertQplus[Q2,\[Beta]];
		{Q1,Q2}
	]
];


GlobalImplicationMinus=Function[{Q,\[Alpha],\[Beta]},
(*It presupposes the existence of an implication \[Alpha]\[Implies]\[Beta] in Q-*)
	Module[{Q1},
		StateTuple`Copy[Q,Q1];
		StateTuple`InsertQplus[Q1,\[Alpha]];
		StateTuple`RemoveQminus[Q1,Implies[\[Alpha],\[Beta]]];
		StateTuple`InsertQminus[Q1,\[Beta]];
		Q1
	]
];



(*Global Disjunction Rules, recalling that \[Phi]\[Or]\[Psi] is defined as an abbreviation of (\[Not]\[Phi])\[Implies]\[Psi]*)
GlobalOrPlus=Function[{Q,\[Phi],\[Psi]},
(*It presupposes the existence of a disjunction \[Phi]\[Or]\[Psi] in Q+*)
	Module[{Q1,Q2},
		StateTuple`Copy[Q,Q1];
		StateTuple`Copy[Q,Q2];
		StateTuple`RemoveQplus[Q1,\[Phi]\[Or]\[Psi]];
		StateTuple`InsertQplus[Q1,\[Phi]];

		StateTuple`RemoveQplus[Q2,\[Phi]\[Or]\[Psi]];
		StateTuple`InsertQplus[Q2,\[Psi]];
		{Q1,Q2}
	]
];


GlobalOrMinus=Function[{Q,\[Phi],\[Psi]},
(*It presupposes the existence of a disjunction \[Phi]\[Or]\[Psi] in Q-*)
	Module[{Q1},
		StateTuple`Copy[Q,Q1];
		StateTuple`RemoveQminus[Q1,\[Phi]\[Or]\[Psi]];		
		StateTuple`InsertQminus[Q1,\[Phi]];
		StateTuple`InsertQminus[Q1,\[Psi]];
		Q1
	]
];


(*Global Conjunction Rules, recalling that \[Phi]\[And]\[Psi] is defined as an abbreviation of (\[Not](\[Phi]\[Implies](\[Not]\[Psi])))*)
GlobalAndPlus=Function[{Q,\[Phi],\[Psi]},
(*It presupposes the existence of a conjunction \[Phi]\[And]\[Psi] in Q+*)
	Module[{Q1},
		StateTuple`Copy[Q,Q1];
		StateTuple`RemoveQplus[Q1,\[Phi]\[And]\[Psi]];		
		StateTuple`InsertQplus[Q1,\[Phi]];
		StateTuple`InsertQplus[Q1,\[Psi]];
		Q1
	]
];


GlobalAndMinus=Function[{Q,\[Phi],\[Psi]},
(*It presupposes the existence of a conjunction \[Phi]\[And]\[Psi] in Q-*)
	Module[{Q1,Q2},
		StateTuple`Copy[Q,Q1];
		StateTuple`Copy[Q,Q2];
		StateTuple`RemoveQminus[Q1,\[Phi]\[And]\[Psi]];
		StateTuple`InsertQminus[Q1,\[Phi]];

		StateTuple`RemoveQminus[Q2,\[Phi]\[And]\[Psi]];
		StateTuple`InsertQminus[Q2,\[Psi]];
		{Q1,Q2}
	]

];



(*Global Negation Rules, recalling that \[Not] is defined as an abbreviation of \[Phi]\[Implies]\[UpTee]*)
GlobalNotPlus=Function[{Q,\[Phi]},
(*It presupposes the existence of a negation \[Not]\[Phi] in Q+*)
	Module[{Q1},
		StateTuple`Copy[Q,Q1];
		StateTuple`RemoveQplus[Q1,\[Not]\[Phi]];		
		StateTuple`InsertQminus[Q1,\[Phi]];
		Q1
	]
];


GlobalNotMinus=Function[{Q,\[Phi]},
(*It presupposes the existence of a negation \[Not]\[Phi] in Q-*)
	Module[{Q1},
		StateTuple`Copy[Q,Q1];
		StateTuple`RemoveQminus[Q1,\[Not]\[Phi]];		
		StateTuple`InsertQplus[Q1,\[Phi]];
		Q1
	]
];


GlobalEquiPlus=Function[{Q,\[Alpha],\[Beta]},
(*It presupposes the existence of an implication \[Alpha]\[Equilibrium]\[Beta] in Q+*)
	Module[{Q1,Q2},
		StateTuple`Copy[Q,Q1];
		StateTuple`Copy[Q,Q2];
		StateTuple`RemoveQplus[Q1,Equivalent[\[Alpha],\[Beta]]];
		StateTuple`InsertQminus[Q1,\[Alpha]];
		StateTuple`InsertQminus[Q1,\[Beta]];

		StateTuple`RemoveQplus[Q2,Equivalent[\[Alpha],\[Beta]]];
		StateTuple`InsertQplus[Q2,\[Alpha]];		
		StateTuple`InsertQplus[Q2,\[Beta]];
		{Q1,Q2}
	]
];


GlobalEquiMinus=Function[{Q,\[Alpha],\[Beta]},
(*It presupposes the existence of an implication \[Alpha]\[Equilibrium]\[Beta] in Q-*)
	Module[{Q1,Q2},
		StateTuple`Copy[Q,Q1];
		StateTuple`Copy[Q,Q2];
		StateTuple`RemoveQminus[Q1,Equivalent[\[Alpha],\[Beta]]];
		StateTuple`InsertQplus[Q1,\[Alpha]];
		StateTuple`InsertQminus[Q1,\[Beta]];

		StateTuple`RemoveQminus[Q2,Equivalent[\[Alpha],\[Beta]]];
		StateTuple`InsertQminus[Q2,\[Alpha]];		
		StateTuple`InsertQplus[Q2,\[Beta]];
		{Q1,Q2}
	]
];


LocalEquiPlus=Function[{Q,i,\[Phi],\[Psi]},
(*It presupposes the existence of an \!\(equivalence\ 
\*SubscriptBox[\(@\), \(i\)]\([\[Phi] \[Equivalent] \[Psi]]\)\) in Q+*)
	Module[{Q1,Q2},
		StateTuple`Copy[Q,Q1];
		StateTuple`Copy[Q,Q2];
		StateTuple`RemoveQplus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi] \[Equivalent] \[Psi]]\)\)];
		StateTuple`InsertQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\)];
		StateTuple`InsertQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]]\)\)];

		StateTuple`RemoveQplus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi] \[Equivalent] \[Psi]]\)\)];
		StateTuple`InsertQplus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\)];
		StateTuple`InsertQplus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]]\)\)];
		{Q1,Q2}
	]
];


LocalEquiMinus=Function[{Q,i,\[Phi],\[Psi]},
(*It presupposes the existence of an \!\(equivalence\ 
\*SubscriptBox[\(@\), \(i\)]\([\[Phi] \[Equivalent] \[Psi]]\)\) in Q-*)
	Module[{Q1,Q2},
		StateTuple`Copy[Q,Q1];
		StateTuple`Copy[Q,Q2];
		StateTuple`RemoveQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi] \[Equivalent] \[Psi]]\)\)];
		StateTuple`InsertQplus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\)];
		StateTuple`InsertQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]]\)\)];

		StateTuple`RemoveQminus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi] \[Equivalent] \[Psi]]\)\)];
		StateTuple`InsertQplus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]]\)\)];
		StateTuple`InsertQminus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\)];
		{Q1,Q2}
	]
];


(*Local Implication Rules*)
LocalImplicationPlus=Function[{Q,i,\[Phi],\[Psi]},
(*It presupposes the existence of an \!\(implication\ 
\*SubscriptBox[\(@\), \(i\)]\([\[Phi] \[Implies] \[Psi]]\)\) in Q+*)
	Module[{Q1,Q2},
		StateTuple`Copy[Q,Q1];
		StateTuple`Copy[Q,Q2];
		StateTuple`RemoveQplus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi] \[Implies] \[Psi]]\)\)];
		StateTuple`InsertQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\)];

		StateTuple`RemoveQplus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi] \[Implies] \[Psi]]\)\)];
		StateTuple`InsertQplus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]]\)\)];
		{Q1,Q2}
	]
];


LocalImplicationMinus=Function[{Q,i,\[Phi],\[Psi]},
(*It presupposes the existence of an \!\(implication\ 
\*SubscriptBox[\(@\), \(i\)]\([\[Phi] \[Implies] \[Psi]]\)\) in Q-*)
	Module[{Q1},
		StateTuple`Copy[Q,Q1];
		StateTuple`InsertQplus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\)];
		StateTuple`RemoveQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi] \[Implies] \[Psi]]\)\)];
		StateTuple`InsertQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]]\)\)];
		Q1
	]
];


(*G Rules*)
GPlus=Function[{Q,i,\[Phi]},
(*It presupposes the existence \!\(of\ 
\*SubscriptBox[\(@\), \(i\)]\([G\ \[Phi]]\)\) in Q+*)
	Module[{Q1},
		StateTuple`Copy[Q,Q1];
		StateTuple`RemoveQplus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([G\ \[Phi]]\)\)];		
		StateTuple`InsertQplus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\)];
		StateTuple`InsertQplus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([X\ \((G\ \[Phi])\)]\)\)];
		Q1
	]
];


GMinus=Function[{Q,i,\[Phi]},
(*It presupposes the existence \!\(of\ 
\*SubscriptBox[\(@\), \(i\)]\([G\ \[Phi]]\)\) in Q-*)
	Module[{Q1,Q2},
		StateTuple`Copy[Q,Q1];
		StateTuple`Copy[Q,Q2];
		StateTuple`RemoveQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([G\ \[Phi]]\)\)];
		StateTuple`InsertQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\)];

		StateTuple`RemoveQminus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([G\ \[Phi]]\)\)];
		StateTuple`InsertQminus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([X\ \((G\ \[Phi])\)]\)\)];
		{Q1,Q2}
	]
];


(*Rules for communication*)
\[Copyright]Plus=Function[{Q,i,j,\[Phi]},
(*It presupposes the existence \!\(of\ 
\*SubscriptBox[\(@\), \(i\)]\([
\(\*SubscriptBox[\(\[Copyright]\), \(j\)]\)[\[Phi]]]\)\) in Q+*)
	Module[{Q1,\[Eta]b,\[Eta]p},
		StateTuple`Copy[Q,Q1];
		\[Eta]b=AuxiliaryFunctions`\[Eta]bowtie[i,j,Q];
		\[Eta]p=AuxiliaryFunctions`\[Eta]plus[i,j,Q];

		Map[StateTuple`RemoveQplus[Q1,#]&,\[Eta]b];
		Map[StateTuple`InsertQplus[Q1,#]&,\[Eta]p];
		StateTuple`InsertQbowtie[Q1,i,j];
		Q1
	]
];


\[Copyright]Minus=Function[{Q,i,j,\[Phi]},
(*It presupposes the existence \!\(of\ 
\*SubscriptBox[\(@\), \(i\)]\([
\(\*SubscriptBox[\(\[Copyright]\), \(j\)]\)[\[Phi]]]\)\) in Q-*)
	Module[{Q1,Q2,\[Eta]h,\[Eta]m},
		StateTuple`Copy[Q,Q1];
		StateTuple`Copy[Q,Q2];
		\[Eta]h=AuxiliaryFunctions`\[Eta]\[NumberSign][i,j,Q];
		\[Eta]m=AuxiliaryFunctions`\[Eta]minus[i,j,Q];

		Map[StateTuple`RemoveQminus[Q1,#]&,\[Eta]h];
		Map[StateTuple`InsertQminus[Q1,#]&,\[Eta]m];
		StateTuple`InsertQbowtie[Q1,i,j];

		Map[StateTuple`RemoveQminus[Q2,#]&,\[Eta]h];
		StateTuple`InsertQ\[NumberSign][Q2,i,j];
		{Q1,Q2}
	]
];


(*Next Rule*)
XRule=Function[{t,Q},
(*It presupposes that all the formulas have been decomposed 
   except for those referring to the next state*)
	Module[{l={},id,i},
	id=Successors[t];
		i=1;
		While[i<=Length[id],
			AppendTo[l,{auxf[t,Q,id[[i]]],id[[i]]}];
			i++;
		];
		l
	]
];


(*Auxiliary functions for the XRule*)
auxf=Function[{t,Q,id},
(*Returns the State Tuple resulting from applying 
	the Local Rule for X to the State Tuple Q with the subset of Identifiers id*)
	Module[{Q1,aux,res},
		Copy[Q,Q1];
		aux=\[Sigma]plus[t,id,Q1];
		res=L[Q1,id];
		Map[RemoveQplus[Q1,#]&,res];
		Map[InsertQplus[Q1,#]&,aux];
		aux=\[Sigma]minus[t,id,Q1];
		Map[RemoveQminus[Q1,#]&,res];
		Map[InsertQminus[Q1,#]&,aux];
		(*ReplaceQX*)
		DeleteQbowtie[Q1];
		DeleteQ\[NumberSign][Q1];
		DeleteQX[Q1];
		Map[InsertQX[Q1,#]&,id];
		Q1
	]
];


L=Function[{Q1,K},
(*Identifies which are the formulas that need to be removed
	\!\(
\*SubscriptBox[\(@\), \(k\)]\([\[Phi]]\)\) | \[Phi]\[Element]Subscript[\[ScriptCapitalL], k] for k\[Element]K *)
	Module[{form,i,aux,l,res={}},
		form=Union[GetQplus[Q1],GetQminus[Q1]];
		i=1;
		aux=form[[Flatten[Map[First,Position[form,Head[\!\(
\*SubscriptBox[\(@\), \(i\)]\(["\<p\>"]\)\)]]]]]];
		While[i<=Length[K],
			l=Flatten[Position[Map[#[[1]]&,aux],K[[i]]]];
			While[l!={},
				AppendTo[res,form[[l[[1]]]]];
				l=Rest[l];

			];
			i++;
		];
		res
	]
];


(*Rules obtained for the abbreviations*)
(*F Rules, recalling that F is defined as an abbreviation F\[Congruent]\[Not]G\[Not]\[Phi]*)
FPlus=Function[{Q,i,\[Phi]},
(*It presupposes the existence \!\(of\ 
\*SubscriptBox[\(@\), \(i\)]\([F\ \[Phi]]\)\) in Q+*)
	Module[{Q1,Q2},
		StateTuple`Copy[Q,Q1];
		StateTuple`Copy[Q,Q2];
		StateTuple`RemoveQplus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([F\ \[Phi]]\)\)];
		StateTuple`InsertQplus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\)];

		StateTuple`RemoveQplus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([F\ \[Phi]]\)\)];
		StateTuple`InsertQplus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([X\ \((F\ \[Phi])\)]\)\)];
		{Q1,Q2}
	]
];


FMinus=Function[{Q,i,\[Phi]},
(*It presupposes the existence \!\(of\ 
\*SubscriptBox[\(@\), \(i\)]\([F\ \[Phi]]\)\) in Q-*)
	Module[{Q1},
		StateTuple`Copy[Q,Q1];
		StateTuple`RemoveQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([F\ \[Phi]]\)\)];		
		StateTuple`InsertQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\)];
		StateTuple`InsertQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([X\ \((F\ \[Phi])\)]\)\)];
		Q1
	]
];


(*Rules for the disjunction recalling that \[Or] is defined as an abbreviation *)
OrPlus=Function[{Q,i,\[Phi],\[Psi]},
(*It presupposes the existence \!\(of\ 
\*SubscriptBox[\(@\), \(i\)]\([\[Phi] \[Or] \[Psi]]\)\) in Q+*)
	Module[{Q1,Q2},
		StateTuple`Copy[Q,Q1];
		StateTuple`Copy[Q,Q2];
		StateTuple`RemoveQplus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([Or[\[Phi], \[Psi]]]\)\)];
		StateTuple`InsertQplus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\)];

		StateTuple`RemoveQplus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([Or[\[Phi], \[Psi]]]\)\)];
		StateTuple`InsertQplus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]]\)\)];
		{Q1,Q2}
	]
];


OrMinus=Function[{Q,i,\[Phi],\[Psi]},
(*It presupposes the existence \!\(of\ 
\*SubscriptBox[\(@\), \(i\)]\([\[Phi] \[Or] \[Psi]]\)\) in Q-*)
	Module[{Q1},
		StateTuple`Copy[Q,Q1];
		StateTuple`RemoveQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([Or[\[Phi], \[Psi]]]\)\)];		
		StateTuple`InsertQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\)];
		StateTuple`InsertQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]]\)\)];
		Q1
	]
];


(*Rules for the conjunction recalling that \[And] is defined as an abbreviation*)
AndPlus=Function[{Q,i,\[Phi],\[Psi]},
(*It presupposes the existence \!\(of\ 
\*SubscriptBox[\(@\), \(i\)]\([\[Phi] \[And] \[Psi]]\)\) in Q+*)
	Module[{Q1},
		StateTuple`Copy[Q,Q1];
		StateTuple`RemoveQplus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([And[\[Phi], \[Psi]]]\)\)];		
		StateTuple`InsertQplus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\)];
		StateTuple`InsertQplus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]]\)\)];
		Q1
	]
];


AndMinus=Function[{Q,i,\[Phi],\[Psi]},
(*It presupposes the existence \!\(of\ 
\*SubscriptBox[\(@\), \(i\)]\([\[Phi] \[And] \[Psi]]\)\) in Q-*)
	Module[{Q1,Q2},
		StateTuple`Copy[Q,Q1];
		StateTuple`Copy[Q,Q2];
		StateTuple`RemoveQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([And[\[Phi], \[Psi]]]\)\)];
		StateTuple`InsertQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\)];

		StateTuple`RemoveQminus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([And[\[Phi], \[Psi]]]\)\)];
		StateTuple`InsertQminus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]]\)\)];
		{Q1,Q2}
	]
];


(*Rules for the negation recalling that \[Not] is defined as an abbreviation of \[Phi]\[Implies]\[UpTee]*)
NotPlus=Function[{Q,i,\[Phi]},
(*It presupposes the existence \!\(of\ 
\*SubscriptBox[\(@\), \(i\)]\([\[Not] \[Phi]]\)\) in Q+*)
	Module[{Q1},
		StateTuple`Copy[Q,Q1];
		StateTuple`RemoveQplus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([Not[\[Phi]]]\)\)];		
		StateTuple`InsertQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\)];
		Q1
	]
];


NotMinus=Function[{Q,i,\[Phi]},
(*It presupposes the existence \!\(of\ 
\*SubscriptBox[\(@\), \(i\)]\([\[Not] \[Phi]]\)\) in Q-*)
	Module[{Q1},
		StateTuple`Copy[Q,Q1];
		StateTuple`RemoveQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([Not[\[Phi]]]\)\)];		
		StateTuple`InsertQplus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\)];
		Q1
	]
];


(*Until Rules*)
UPlus=Function[{Q,i,\[Phi],\[Psi]},
(*It presupposes the existence \!\(of\ 
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]U\[Psi]]\)\) in Q+*)
	Module[{Q1,Q2},
		StateTuple`Copy[Q,Q1];
		StateTuple`Copy[Q,Q2];
		StateTuple`RemoveQplus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]\ \[GothicCapitalU]\ \[Psi]]\)\)];
		StateTuple`InsertQplus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]]\)\)];

		StateTuple`RemoveQplus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]\ \[GothicCapitalU]\ \[Psi]]\)\)];
		StateTuple`InsertQplus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\)];		
		StateTuple`InsertQplus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([X\ \((\[Phi]\ \[GothicCapitalU]\ \[Psi])\)]\)\)];
		{Q1,Q2}
	]
];


UMinus=Function[{Q,i,\[Phi],\[Psi]},
(*It presupposes the existence \!\(of\ 
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]U\[Psi]]\)\) in Q-*)
	Module[{Q1,Q2},
		StateTuple`Copy[Q,Q1];
		StateTuple`Copy[Q,Q2];
		StateTuple`RemoveQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]\ \[GothicCapitalU]\ \[Psi]]\)\)];
		StateTuple`InsertQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\)];		
		StateTuple`InsertQminus[Q1,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]]\)\)];

		StateTuple`RemoveQminus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]\ \[GothicCapitalU]\ \[Psi]]\)\)];
		StateTuple`InsertQminus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]]\)\)];		
		StateTuple`InsertQminus[Q2,\!\(
\*SubscriptBox[\(@\), \(i\)]\([X\ \((\[Phi]\ \[GothicCapitalU]\ \[Psi])\)]\)\)];
		{Q1,Q2}
	]
];


End[];
EndPackage[]
