(* ::Package:: *)

BeginPackage["StateTuple`",{"Formulas`"}];

NewStateTuple::usage="NewStateTuple[Q,Qplus,Qminus,Qbowtie,Q\[NumberSign],QX] creates a new State Tuple, referenced as Q, verifiyng if the arguments are of the correct type.";
StateTuple::usage="StateTuple[Q] creates an empty StateTuple, referenced as Q.
StateTuple[Q,Qplus,Qminus,Qbowtie,Q\[NumberSign],QX] creates a new StateTuple, referenced as Q, with the sets from input, withouth verifying them.";

StateTupleQ::usage="StateTupleQ[Q] returns True if Q is a well-formed State Tuple and False otherwise.";
StateQ::usage="StateQ[Q]returns True if Q is a State and False otherwise.";

Copy::usage="Copy[Q1,Q2] creates a copy of StateTuple Q1 refereced as Q2.";
PrintST::usage="PrintST[Q] prints the StateTuple Q, without disclosing the implementation details.";

Identifiers::usage="Identifiers[Q] returns the universe of agents identifiers of StateTuple Q.";

InsertQplus::usage="InsertQplus[Q,\[Alpha]] inserts the formula \[Alpha] in the first set of the StateTuple Q.
Assumes Q a well-formed ST, but checks if \[Alpha] is a well-formed formula.";
InsertQminus::usage="InsertQminus[Q,\[Alpha]] inserts the formula \[Alpha] in the second set of the StateTuple Q.
Assumes Q a well-formed ST, but checks if \[Alpha] is a well-formed formula.";
InsertQbowtie::usage="InsertQbowtie[Q,i,j] inserts the pair of agents (i,j) in the set of forced synchronizations of the StateTuple Q.";
InsertQ\[NumberSign]::usage="InsertQ\[NumberSign][Q,i,j] inserts the pair of agents (i,j) in the set of conflicts of the StateTuple Q.";
InsertQX::usage="InsertQX[Q,i] inserts the agent i in the set of the synchronized agents of the StateTuple Q.";

RemoveQplus::usage="RemoveQplus[Q,f] removes the Formula f from the set Qplus, of the StateTuple Q.";
RemoveQminus::usage="RemoveQminus[Q,f] removes the Formula f from the set Qminus, of the StateTuple Q.";

GetQplus::usage="GetQplus[Q] returns the first set of the StateTuple Q, assuming it is well-formed, and without disclosing the implementation details.";
GetQminus::usage="GetQminus[Q] returns the second set of the StateTuple Q, assuming it is well-formed, and without disclosing the implementation details.";"";
GetQbowtie::usage="GetQbowtie[Q] returns the set of forced synchronizations of the StateTuple Q, assuming it is well-formed, and without disclosing the implementation details.";
GetQ\[NumberSign]::usage="GetQ\[NumberSign][Q] returns the set of conflicts the StateTuple Q, assuming it is well-formed, and without disclosing the implementation details.";
GetQX::usage="GetQX[Q] returns the set of synchronized agents of the StateTuple Q, assuming it is well-formed, and without disclosing the implementation details.";

ContradictoryQ::usage="ContradictoryQ[Q] returns true if Q is a contradictory StateTuple and False otherwise.";
Successors::usage="Successors[t] returns the list of all subsets of agents identifiers of t.";


STpos::usage="STpos[Q,t,b] returns 0 if there is no formulas of the type t in the set b of the StateTuple Q, if there are, it returns the position of the first.
The t can be one of the following Strings:
	GlobalBoolean, GlobalImplication, GlobalDisjunction, GlobalNegation, GlobalConjunction, GlobalEquivalence, 
	Boolean, Implication, Globally, Eventually, Next, Until, Negation, Disjunction, Conjunction, Communication, Proposition, Equivalence
The b is a Boolean: True for the first set and False for the second.";
STSubParts::usage="STSubParts[Q,t,b] returns an empty set if there is no formulas of the type t in the set b of the StateTuple Q, if there are, it returns the set of the SubParts of the first.
The t can be one of the following Strings:
	GlobalBoolean, GlobalImplication, GlobalDisjunction, GlobalNegation, GlobalConjunction, GlobalEquivalence, 
	Boolean, Implication, Globally, Eventually, Next, Until, Negation, Disjunction, Conjunction, Communication, Proposition, Equivalence
The b is a Boolean: True for the first set and False for the second.";


EqualsQ::usage="EqualsQ[Q1,Q2] returns True if Q1 and Q2 have the same formulas and synchronization requirements, and False otherwise.";

RemoveQbowtie::usage="RemoveQbowtie[Q,val1,val2] removes the pair (val1,val2) from the set of forced synchronizations of the StateTuple Q.";
RemoveQ\[NumberSign]::usage="RemoveQ\[NumberSign][Q,val1,val2] removes the pair (val1,val2) from the set of conflicts of the StateTuple Q.";
RemoveQX::usage="RemoveQX[Q,val] removes val from the set of synchronized agents of StateTuple Q.";

DeleteQbowtie::usage="DeleteQbowtie[Q] empties the set of forced synchronizations of the StateTuple Q.";
DeleteQ\[NumberSign]::usage="DeleteQ\[NumberSign][Q_] empties the set of conflicts of the StateTuple Q.";
DeleteQX::usage="DeleteQX[Q_] empties the set of synchronized agents of StateTuple Q.";



Begin["`Private`"];


SetAttributes[{NewStateTuple,StateTuple,StateTupleQ,Identifiers,GetQX,GetQ\[NumberSign],GetQbowtie,GetQplus,GetQminus,
ContradictoryQ,PrintST,RemoveQminus,RemoveQplus,RemoveQbowtie,RemoveQ\[NumberSign],RemoveQX,Copy,StateQ,STpos,STSubParts,
InsertQplus,InsertQminus,InsertQbowtie,InsertQ\[NumberSign],InsertQX,DeleteQbowtie,DeleteQ\[NumberSign],DeleteQX,EqualsQ},ReadProtected];


NewStateTuple[Q_,Qplus_,Qminus_,Qbowtie_,Q\[NumberSign]_,QX_]:=(
(*Creates the StateTuple Q*)
		StateTuple[Q,Qplus,Qminus,Qbowtie,Q\[NumberSign],QX];
(*Verifies if the set are of the required form, and if the formulas are well-formed*)
		StateTupleQ[Q];
);


StateTuple[Q_]:=
(*Creates an empty StateTuple*)
	(Q["Qplus"]={};
	Q["Qminus"]={};
	Q["Qbowtie"]={};
	Q["Q\[NumberSign]"]={};
	Q["QX"]={});


StateTuple[Q_,Qplus_,Qminus_,Qbowtie_,Q\[NumberSign]_,QX_]:=(
(*Creates the StateTuple Q with the set from input*)
		Q["Qplus"]=Sort[Qplus];				
		Q["Qminus"]=Sort[Qminus];
		Q["Qbowtie"]=Sort[Qbowtie];
		Q["Q\[NumberSign]"]=Sort[Q\[NumberSign]];
		Q["QX"]=Sort[QX];
(*We have sorted the sets in order to more efficiently insert and delete elements*)
);


StateTupleQ=Function[{Q},
(*Verifies if the StateTuple and its formulas are of the required form. 
Definition 4.1*)
	Which[
		!Apply[And,Map[FormulaQ,Q["Qplus"]]],
			False, (*There is a not well-formed formula in Qplus*)
		!Apply[And,Map[FormulaQ,Q["Qminus"]]],
			False, (*There is a not well-formed formula in Qminus*)
		!((!ListQ[Q["Qbowtie"]])||Apply[And,Map[Length[#]==2&,Q["Qbowtie"]]]),
			False, (*Qbowtie is not of the form required*)
		!((!ListQ[Q["Q\[NumberSign]"]])||Apply[And,Map[Length[#]==2&,Q["Q\[NumberSign]"]]]),
			False, (*Q\[NumberSign] is not of the form required*)
		!ListQ[Q["QX"]],
			False, (*QX is not of the form required*)
		True,
			True
	]
];


StateQ=Function[{Q},
(*Definition 4.2*)
	Module[{Q1,b=False},
		Q1=Union[Q["Qplus"],Q["Qminus"]];
		b=Apply[And,Map[StateFormulaQ,Q1]]; (*StateFormulaQ from package Formulas.m*)
		b
	]
];


Copy[Q1_,Q2_]:=
(*Does not check if Q1 is a well-formed StateTuple*)
	StateTuple[Q2,GetQplus[Q1],GetQminus[Q1],GetQbowtie[Q1],GetQ\[NumberSign][Q1],GetQX[Q1]];


ContradictoryQ=Function[Q,
(*Definition 4.3*)
	Which[
		Apply[Or,Apply[And,Map[MemberQ[Q["QX"],#]&,Q["Q\[NumberSign]"],{2}],2]],
			True,
		Apply[Or,Apply[Or,Map[!MemberQ[Q["QX"],#]&,Q["Qbowtie"],{2}],2]],
			True,
		IntersectingQ[Q["Qplus"],Q["Qminus"]],
			True,
		!Apply[And,Flatten[Map[SubParts[#,"BooleanQ"]&,Select[Q["Qplus"],(FormulaType[#]=="Boolean")&]]]],
(*There is \!\(an\ 
\*SubscriptBox[\(@\), \(i\)]\([False]\)\) in Qplus*)
			True,
		!Apply[And,Select[Q["Qplus"],(FormulaType[#]=="GlobalBoolean")&]],
(*There is a False in Qplus*)
			True,
		Apply[Or,Flatten[Map[SubParts[#,"BooleanQ"]&,Select[Q["minus"],(FormulaType[#]=="Boolean")&]]]],
(*There is \!\(an\ 
\*SubscriptBox[\(@\), \(i\)]\([True]\)\) in Qminus*)
			True,
		Apply[Or,Select[Q["minus"],(FormulaType[#]=="GlobalBoolean")&]],
(*There is a True in Qminus*)
			True,
		True,
			False
	]
		
];


PrintST[Q_]:=
(*Transforms a StateTuple into a String, same notation as Definition 4.1*)
	Return["<"<>ToString[Q["Qplus"],StandardForm]<>
			","<>ToString[Q["Qminus"],StandardForm]<>
			","<>ToString[Q["Qbowtie"]]<>
			","<>ToString[Q["Q\[NumberSign]"]]<>
			","<>ToString[Q["QX"]]<>">"];


Identifiers=Function[Q,
(*Gets the universe of agents identifiers of Q*)
	Module[{Q1,id,pairs},
		id=GetQX[Q];
		pairs=Union[GetQ\[NumberSign][Q],GetQbowtie[Q]];
		id=Union[id,Union[Flatten[pairs]]];
		Q1=Union[GetQplus[Q],GetQminus[Q]];
		Union[Flatten[Map[Ident[#,{}]&,Q1]],id] (*Function Ident from Formulas.m*)
	]
];


(*IdentifierQ=Function[{t,I},
(*NAO FAZ SENTIDO*)
	Apply[And,Map[MemberQ[t["id"],#]&,I]]];*)


InsertQplus[Q_,value_]:=
(*Assumes Q well-formed*)
	If[FormulaQ[value],
		Q["Qplus"]=Union[Q["Qplus"],{value}],
		Print[value, " is not a formula."]
(*Mantains the set sorted*)
];


InsertQminus[Q_,value_]:=
(*Assumes Q well-formed*)
	If[FormulaQ[value],
		Q["Qminus"]=Union[Q["Qminus"],{value}],
		Print[value, " is not a formula."]
(*Mantains the set sorted*)
];


InsertQbowtie[Q_,value1_,value2_]:=
(*Assumes Q well-formed*)
	If[(!MemberQ[Q["Qbowtie"],{value1,value2}])
		&&(!MemberQ[Q["Qbowtie"],{value2,value1}]),
			Q["Qbowtie"]=Union[Q["Qbowtie"],{{value1,value2}}]
(*Mantains the set sorted*)
];


InsertQX[Q_,value_]:=
(*Assumes Q well-formed*)
	Q["QX"]=Union[Q["QX"],{value}];
(*Mantains the set sorted*)


RemoveQplus[Q_,value_]:=
	Q["Qplus"]=Complement[Q["Qplus"],{value}];
(*If present, removes the value from Qplus. Qplus remains sorted*)


RemoveQminus[Q_,value_]:=
	Q["Qminus"]=Complement[Q["Qminus"],{value}];
(*If present, removes the value from Qminus. Qminus remains sorted*)


RemoveQbowtie[Q_,value1_,value2_]:=
	(Q["Qbowtie"]=Complement[Q["Qbowtie"],{{value1,value2}}];
	Q["Qbowtie"]=Complement[Q["Qbowtie"],{{value2,value1}}]);


RemoveQ\[NumberSign][Q_,value1_,value2_]:=
	(Q["Q\[NumberSign]"]=Complement[Q["Q\[NumberSign]"],{{value1,value2}}];
	Q["Q\[NumberSign]"]=Complement[Q["Q\[NumberSign]"],{{value2,value1}}]);


RemoveQX[Q_,value_]:=
	Q["QX"]=Complement[Q["QX"],{value}];


(*Empties the set Qbowtie*)
DeleteQbowtie[Q_]:=(Q["Qbowtie"]={});


(*Empties the set Q\[NumberSign]*)
DeleteQ\[NumberSign][Q_]:=(Q["Q\[NumberSign]"]={});


(*Empties the set QX*)
DeleteQX[Q_]:=(Q["QX"]={});


(*Returns the set Qplus*)
GetQplus[Q_]:=Q["Qplus"];


(*Returns the set Qminus*)
GetQminus[Q_]:=Q["Qminus"];


(*Returns the set Qbowtie*)
GetQbowtie[Q_]:=Q["Qbowtie"];


(*Returns the set Q\[NumberSign]*)
GetQ\[NumberSign][Q_]:=Q["Q\[NumberSign]"];


(*Returns the set QX*)
GetQX[Q_]:=Q["QX"];


STpos=Function[{ST,type,positive},
(*Assume-se ST bem definido, type uma das strings suposta e positive um boolean*)
Module[{list,l,i,notFound},
	If[positive,list=GetQplus[ST],list=GetQminus[ST]];
	i=1;
	notFound=True;
	While[notFound&&i<=Length[list],
		If[FormulaType[list[[i]]]==type,
			notFound=False
		];
		i++;
	];
	If[notFound,0,i-1]
]];


STSubParts=Function[{ST,type,positive},
	Module[{list,pos},
		If[positive,list=GetQplus[ST],list=GetQminus[ST]];
		pos=STpos[ST,type,positive]; (*0 if inexistent*)
		If[pos!=0,
			SubParts[list[[pos]],type], (*SubParts froms Formulas.m*)
			{}
		]
]];


EqualsQ=Function[{Q1,Q2},
	Sort[GetQplus[Q1]]===Sort[GetQplus[Q2]]&&
	Sort[GetQminus[Q1]]===Sort[GetQminus[Q2]]&&
	Sort[GetQ\[NumberSign][Q1]]===Sort[GetQ\[NumberSign][Q2]]&&
	Sort[GetQbowtie[Q1]]===Sort[GetQbowtie[Q2]]&&
	Sort[GetQX[Q1]]===Sort[GetQX[Q2]]
];


Successors=Function[{t},
(*Subsets of agents identifiers*)
	Module[{ident},
		ident=t["id"];
		Subsets[ident,{1,Length[ident]}]
]];


End[];
EndPackage[]
