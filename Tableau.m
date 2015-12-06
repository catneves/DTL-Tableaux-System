(* ::Package:: *)

BeginPackage["Tableau`",{"Formulas`","StateTuple`","Rules`"}];

Tableau::usage="Tableau[t,Q] creates a new Tableau, referenced as t, with StateTuple Q as root.";
TableauQ::usage="TableauQ[t] returns True if t is a well-formed Tableau and False otherwise,";
SuccessfulQ::usage="SuccessfulQ[t] returns True if t is succesfull and False otherwise.";
ClosedQ::usage="ClosedQ[t,Q] returns True if the StateTuple Q is closed in the Tableau t.";
Closure::usage="Closure[t,s] verifies if the state tuple s is closed or not. If it is adds it to the set of closed nodes.";
Iterate::usage="Iterate[t] apply all the rules defined, until there is no more rules appliable";
Rules::usage="Rules[t] apply a rule at a time.";
ApplyRule::usage="ApplyRule[t,Q,r] makes the transference of information to the Graph. t is the tableau Q is the StateTuple and r is the name of the rule applied.";
Child::usage="Child[t,Q] returns a list of childs of the State Tuple Q in the tableau t.";
Parents::usage="Parents[t,Q] returns a list of parents of the State Tuple Q in the tableau t.";

NotClosed::usage="NotClosed[t] returns the list os state tuples that are not closed in the tableau t";
GetId::usage="GetId[t] returns the list of agents identifiers.";
Legend::usage="Prints the legend of the tableau.";
PrintNST::usage="PrintNST[t,Q] prints the state tuple Q from the tableau t.";


State::usage="State[t,s] returns the State Tuple that corresponds o the string s.";
Begin["`Private`"];


SetAttributes[{Tableau,State,PrintNST,Legend,
				GetId,NotClosed,Parents,Child,ApplyRule,Rules,Iterate,Closure,ClosedQ,
SuccessfulQ,TableauQ},ReadProtected];


PrintNST[t_,Q_]:=Lookup[t["hash"],Q][[1]];


Tableau=Function[{t,s},
	Module[{print},
		print=PrintST[s];
		If[GetQX[s]!={},t["X"]={print},t["X"]={}];
		If[ContradictoryQ[s],
			t["closed"]={print};t["visit"]={},
			t["closed"]={};t["visit"]={print}
		];

		t["g"]:=Graph[{print\[DirectedEdge]print},VertexLabels->"Index"];
		t["hash"]:=Association[print->{1,s}];
		t["index"]=2;
		t["id"]=Identifiers[s];
	]
];


TableauQ=Function[t,
(*Verification of the structure*)
	And[
		ListQ[t["X"]],
		ListQ[t["closed"]],
		ListQ[t["visit"]],
		GraphQ[t["g"]],
		AssociationQ[t["hash"]],
		IntegerQ[t["index"]],
		ListQ[t["id"]]
	]
];


SuccessfulQ=Function[t,
(*Root is closed?*)
	!ClosedQ[t,VertexList[t["g"]][[1]]]
];


ClosedQ=Function[{t,s},
(*Set of closed nodes of t*)
	MemberQ[t["closed"],s]
];


State=Function[{t,s},
(*Correspondence between the StateTuple and its String*)
	Lookup[t["hash"],s][[2]]
];


Closure=Function[{t,s},
(*Definition 4.7*)
(*C1 is not necessary as it is verified evertime a StateTuple is added to the Tableau*)
Module[{state,b2},
	state=Lookup[t["hash"],s][[2]];
Scan[If[ClosedQ[t,#],b2=True,b2=False;Return[]]&,Child[t,s]];
	Which[
		(*C2*)
		b2,
			t["closed"]=Union[t["closed"],{s}],
		(*C3*)
		c3[t,state],
			t["closed"]=Union[t["closed"],{s}],
		(*C5*)
		c5[t,state],
			t["closed"]=Union[t["closed"],{s}],
		(*C6*)
		c6[t,state],
			t["closed"]=Union[t["closed"],{s}],
		(*C4*)
		c4[t,s],
			t["closed"]=Union[t["closed"],{s}]
	]
]];


c4 = Function[{t, s},
(*Check if the is a path between s and the nodes in t["X"], if so if they have a closed node*)
	Module[{iIdentifiers,states,b = True,id,STsWithIdInQX = {}, ii, l,inc,lst,jj},
	Catch[
		iIdentifiers = 1; (*Fix the i, search the states with i in QX*)
		states=Child[t,s];
		If[states == {},Throw[False]]; (*If there are no kids, there is no need to do the verification*)
		If[states == {s},Throw[False]]; (*Neither if the only child is itself*)
(*states is now free, can be re-asignd*)
		states=Map[Lookup[t["hash"],#][[2]]&,t["X"]];
    	While[iIdentifiers <= Length[t["id"]] && b,
			b = False;
			id = t["id"][[iIdentifiers]];
			STsWithIdInQX = Map[t["X"][[#]]&, 
								Map[First,Position[Map[GetQX,states], id, 2]]];
			lst= Length[STsWithIdInQX];
			For[inc = 1, inc <= lst && ! b, inc++,
				For[jj = 1, jj <= Length[VertexList[t["g"]]] && ! b, jj++,
					l = FindPath[t["g"], s, STsWithIdInQX[[inc]], {jj}, All];
					For[ii = 1, ii <= Length[l] && ! b, ii++,
						Scan[If[ClosedQ[t, #],b=True;Return[],b=False]&,Rest[l[[ii]]]];
						b=!b
         			];
        		]
			];
			iIdentifiers++;
		];
    	Throw[! b]
	]
    ]
];


ApplyRule=Function[{t,state,r},
	Module[{m,f,pos,s},
		s=PrintST[state];
		m=VertexList[t["g"]];
		If[VertexCount[t["g"]]==1,(*Only want to do this in the first one*)
			t["g"]=EdgeDelete[t["g"],a_\[DirectedEdge]a_]
		];
		f=Lookup[t["hash"],s,False];
(*Is the State Tuple already in the tableau?*)
		If[f===False,
			(t["g"]=EdgeAdd[t["g"],{First[t["visit"]]\[DirectedEdge]s}];
			t["g"]=SetProperty[{t["g"],First[t["visit"]]\[DirectedEdge]s},EdgeLabels->r];
			AppendTo[t["hash"],s->{t["index"],state}];
(*Rules are only applied to non-contradictory StateTuples*)
			If[!ContradictoryQ[state],AppendTo[t["visit"],s],AppendTo[t["closed"],s]];
			If[GetQX[state]!={},AppendTo[t["X"],s]];
			t["index"]++
			),
			((*The state tuple was already in the graph*)
			pos=f[[1]];
			t["g"]=EdgeAdd[t["g"],{First[t["visit"]]\[DirectedEdge]m[[pos]]}];
			t["g"]=SetProperty[{t["g"],First[t["visit"]]\[DirectedEdge]m[[pos]]},EdgeLabels->r];
			)
		];
	]
];


Rules[t_]:=(
(*Apply one rule at a time*)
(*Function that applies Rules until the visit's list is empty is Iterate*)
	Module[{Q1,state,Q2,aux,i},
		Q1=First[t["visit"]];
		state=Lookup[t["hash"],Q1][[2]];
		Which[
(*Global Rules Are Applied First*)
(*GLOBAL RULES THAT CREATE ONLY ONE STATE*)
			STpos[state,"GlobalImplication",False]!=0,
				(
				Q2=Apply[GlobalImplicationMinus,Flatten[{state,STSubParts[state,"GlobalImplication",False]}]];
				ApplyRule[t,Q2,Superscript["\[Implies]","-"]];
				t["visit"]=Rest[t["visit"]];
				),
			STpos[state,"GlobalNegation",False]!=0,
				(
				Q2=Apply[GlobalNotMinus,Flatten[{state,STSubParts[state,"GlobalNegation",False]}]];
				ApplyRule[t,Q2,Superscript["\[Not]","-"]];
				t["visit"]=Rest[t["visit"]];
				),
			STpos[state,"GlobalNegation",True]!=0,
				(
				Q2=Apply[GlobalNotPlus,Flatten[{state,STSubParts[state,"GlobalNegation",True]}]];
				ApplyRule[t,Q2,Superscript["\[Not]","+"]];
				t["visit"]=Rest[t["visit"]];
				),
			STpos[state,"GlobalDisjunction",False]!=0,
				(
				Q2=Apply[GlobalOrMinus,Flatten[{state,STSubParts[state,"GlobalDisjunction",False]}]];
				ApplyRule[t,Q2,Superscript["\[Or]","-"]];
				t["visit"]=Rest[t["visit"]];
				),
			STpos[state,"GlobalConjunction",True]!=0,
				(
				Q2=Apply[GlobalAndPlus,Flatten[{state,STSubParts[state,"GlobalConjunction",True]}]];
				ApplyRule[t,Q2,Superscript["\[And]","+"]];
				t["visit"]=Rest[t["visit"]];
				),

(*GLOBAL RULES THAT CREATE TWO STATES*)
			STpos[state,"GlobalEquivalence",True]!=0,
				(
				Q2=Apply[GlobalEquiPlus,Flatten[{state,STSubParts[state,"GlobalEquivalence",True]}]];
				ApplyRule[t,Q2[[1]],Superscript["\[Equivalent]","+"]];
				ApplyRule[t,Q2[[2]],Superscript["\[Equivalent]","+"]];
				t["visit"]=Rest[t["visit"]];
				),	
			STpos[state,"GlobalEquivalence",False]!=0,
				(
				Q2=Apply[GlobalEquiMinus,Flatten[{state,STSubParts[state,"GlobalEquivalence",False]}]];
				ApplyRule[t,Q2[[1]],Superscript["\[Equivalent]","-"]];
				ApplyRule[t,Q2[[2]],Superscript["\[Equivalent]","-"]];
				t["visit"]=Rest[t["visit"]];
				),		

			STpos[state,"GlobalImplication",True]!=0,
				(
				Q2=Apply[GlobalImplicationPlus,Flatten[{state,STSubParts[state,"GlobalImplication",True]}]];
				ApplyRule[t,Q2[[1]],Superscript["\[Implies]","+"]];
				ApplyRule[t,Q2[[2]],Superscript["\[Implies]","+"]];
				t["visit"]=Rest[t["visit"]];
				),
			
			STpos[state,"GlobalDisjunction",True]!=0,
				(
				Q2=Apply[GlobalOrPlus,Flatten[{state,STSubParts[state,"GlobalDisjunction",True]}]];
				ApplyRule[t,Q2[[1]],Superscript["\[Or]","+"]];
				ApplyRule[t,Q2[[2]],Superscript["\[Or]","+"]];
				t["visit"]=Rest[t["visit"]];
				),
			STpos[state,"GlobalConjunction",False]!=0,
				(
				Q2=Apply[GlobalAndMinus,Flatten[{state,STSubParts[state,"GlobalConjunction",False]}]];
				ApplyRule[t,Q2[[1]],Superscript["\[And]","+"]];
				ApplyRule[t,Q2[[2]],Superscript["\[And]","+"]];
				t["visit"]=Rest[t["visit"]];
				),
				
(*LOCAL RULES THAT CREATE ONLY ONE STATE*)
			STpos[state,"Implication",False]!=0,
				(
				aux=Flatten[{state,STSubParts[state,"Implication",False]}];
				Q2=Apply[LocalImplicationMinus,aux];
				ApplyRule[t,Q2,Subsuperscript["\[Implies]",ToString[aux[[2]]],"-"]];
				t["visit"]=Rest[t["visit"]];
				),
			STpos[state,"Negation",False]!=0,
				(
				aux=Flatten[{state,STSubParts[state,"Negation",False]}];
				Q2=Apply[NotMinus,aux];
				ApplyRule[t,Q2,Subsuperscript["\[Not]",ToString[aux[[2]]],"-"]];
				t["visit"]=Rest[t["visit"]];
				),	
			STpos[state,"Negation",True]!=0,		
				(
				aux=Flatten[{state,STSubParts[state,"Negation",True]}];
				Q2=Apply[NotPlus,aux];
				ApplyRule[t,Q2,Subsuperscript["\[Not]",ToString[aux[[2]]],"+"]];
				t["visit"]=Rest[t["visit"]];
				),
			STpos[state,"Disjunction",False]!=0,	
				(
				aux=Flatten[{state,STSubParts[state,"Disjunction",False]}];
				Q2=Apply[OrMinus,aux];
				ApplyRule[t,Q2,Subsuperscript["\[Or]",ToString[aux[[2]]],"-"]];
				t["visit"]=Rest[t["visit"]];
				),
			STpos[state,"Conjunction",True]!=0,
				(
				aux=Flatten[{state,STSubParts[state,"Conjunction",True]}];
				Q2=Apply[AndPlus,aux];
				ApplyRule[t,Q2,Subsuperscript["\[And]",ToString[aux[[2]]],"+"]];
				t["visit"]=Rest[t["visit"]];
				),
			STpos[state,"Globally",True]!=0,
				(
				aux=Flatten[{state,STSubParts[state,"Globally",True]}];
				Q2=Apply[GPlus,aux];
				ApplyRule[t,Q2,Subsuperscript["G",ToString[aux[[2]]],"+"]];
				t["visit"]=Rest[t["visit"]];
				),
			STpos[state,"Eventually",False]!=0,
				(
				aux=Flatten[{state,STSubParts[state,"Eventually",False]}];
				Q2=Apply[FMinus,aux];
				ApplyRule[t,Q2,Subsuperscript["F",ToString[aux[[2]]],"-"]];
				t["visit"]=Rest[t["visit"]];
				),
			STpos[state,"Communication",True]!=0,
				(
				aux=Flatten[{state,STSubParts[state,"Communication",True]}];
				Q2=Apply[\[Copyright]Plus,aux];
				ApplyRule[t,Q2,Subsuperscript["\[Copyright]",ToString[aux[[2]]],"+"]];
				t["visit"]=Rest[t["visit"]];
				),
(*LOCAL RULES THAT CREATE MORE STATES*)
			STpos[state,"Implication",True]!=0,
				(
				aux=Flatten[{state,STSubParts[state,"Implication",True]}];
				Q2=Apply[LocalImplicationPlus,aux];
				ApplyRule[t,Q2[[1]],Subsuperscript["\[Implies]",ToString[aux[[2]]],"+"]];
				ApplyRule[t,Q2[[2]],Subsuperscript["\[Implies]",ToString[aux[[2]]],"+"]];
				t["visit"]=Rest[t["visit"]];
				),
			STpos[state,"Equivalence",True]!=0,
				(
				aux=Flatten[{state,STSubParts[state,"Equivalence",True]}];
				Q2=Apply[LocalEquiPlus,aux];
				ApplyRule[t,Q2[[1]],Subsuperscript["\[Equivalent]",ToString[aux[[2]]],"+"]];
				ApplyRule[t,Q2[[2]],Subsuperscript["\[Equivalent]",ToString[aux[[2]]],"+"]];
				t["visit"]=Rest[t["visit"]];
				),
			STpos[state,"Equivalence",False]!=0,
				(
				aux=Flatten[{state,STSubParts[state,"Equivalence",False]}];
				Q2=Apply[LocalEquiMinus,aux];
				ApplyRule[t,Q2[[1]],Subsuperscript["\[Equivalent]",ToString[aux[[2]]],"-"]];
				ApplyRule[t,Q2[[2]],Subsuperscript["\[Equivalent]",ToString[aux[[2]]],"-"]];
				t["visit"]=Rest[t["visit"]];
				),
			STpos[state,"Disjunction",True]!=0,
				(
				aux=Flatten[{state,STSubParts[state,"Disjunction",True]}];
				Q2=Apply[OrPlus,aux];
				ApplyRule[t,Q2[[1]],Subsuperscript["\[Or]",ToString[aux[[2]]],"+"]];
				ApplyRule[t,Q2[[2]],Subsuperscript["\[Or]",ToString[aux[[2]]],"+"]];
				t["visit"]=Rest[t["visit"]];
				),
			STpos[state,"Conjunction",False]!=0,
				(
				aux=Flatten[{state,STSubParts[state,"Conjunction",False]}];
				Q2=Apply[AndMinus,aux];
				ApplyRule[t,Q2[[1]],Subsuperscript["\[And]",ToString[aux[[2]]],"-"]];
				ApplyRule[t,Q2[[2]],Subsuperscript["\[And]",ToString[aux[[2]]],"-"]];
				t["visit"]=Rest[t["visit"]];
				),
			STpos[state,"Globally",False]!=0,
				(
				aux=Flatten[{state,STSubParts[state,"Globally",False]}];
				Q2=Apply[GMinus,aux];
				ApplyRule[t,Q2[[1]],Subsuperscript["G",ToString[aux[[2]]],"-"]];
				ApplyRule[t,Q2[[2]],Subsuperscript["G",ToString[aux[[2]]],"-"]];
				t["visit"]=Rest[t["visit"]];
				),
			STpos[state,"Eventually",True]!=0,
				(
				aux=Flatten[{state,STSubParts[state,"Eventually",True]}];
				Q2=Apply[FPlus,aux];
				ApplyRule[t,Q2[[1]],Subsuperscript["F",ToString[aux[[2]]],"+"]];
				ApplyRule[t,Q2[[2]],Subsuperscript["F",ToString[aux[[2]]],"+"]];
				t["visit"]=Rest[t["visit"]];
				),
			STpos[state,"Communication",False]!=0,
				(
				aux=Flatten[{state,STSubParts[state,"Communication",False]}];
				Q2=Apply[\[Copyright]Minus,aux];
				ApplyRule[t,Q2[[1]],Subsuperscript["\[Copyright]",ToString[aux[[2]]],"-"]];
				ApplyRule[t,Q2[[2]],Subsuperscript["\[Copyright]",ToString[aux[[2]]],"-"]];
				t["visit"]=Rest[t["visit"]];
				),
			STpos[state,"Until",True]!=0,
				(
				aux=Flatten[{state,STSubParts[state,"Until",True]}];
				Q2=Apply[UPlus,aux];
				ApplyRule[t,Q2[[1]],Subsuperscript["\[ScriptCapitalU]",ToString[aux[[2]]],"+"]];
				ApplyRule[t,Q2[[2]],Subsuperscript["\[ScriptCapitalU]",ToString[aux[[2]]],"+"]];
				t["visit"]=Rest[t["visit"]];
				),
			STpos[state,"Until",False]!=0,
				(
				aux=Flatten[{state,STSubParts[state,"Until",False]}];
				Q2=Apply[UMinus,aux];
				ApplyRule[t,Q2[[1]],Subsuperscript["\[ScriptCapitalU]",ToString[aux[[2]]],"-"]];
				ApplyRule[t,Q2[[2]],Subsuperscript["\[ScriptCapitalU]",ToString[aux[[2]]],"-"]];
				t["visit"]=Rest[t["visit"]];
				),
			
(*Rule for the next operator*)
			StateQ[state],(*provided that Q is a State*)
				(
				aux=Rules`XRule[t,state];
				i=1;
				While[i<=Length[aux],
					ApplyRule[t,aux[[i,1]],Subscript["X",ToString[aux[[i,2]]]]];
					i++;
				];
				t["visit"]=Rest[t["visit"]];
				)
		];
	]
);


Iterate=Function[t,
(*Applies the function Rules until the vist list is empty*)
	Module[{i=1,j=-1,open},
		While[t["visit"]!={},
			Rules[t];
		];
		While[j!=Length[t["closed"]],
			j=Length[t["closed"]];
			open=NotClosed[t];
			i=Length[open];
			While[i>0,
				Closure[t,open[[i]]];
				i--;
			];
	];
HighlightGraph[t["g"],t["closed"]]
]];


Child=Function[{t,s},ReplaceList[s,EdgeRules[t["g"]]]];	
(*Returns all the direct childs of s*)


Parents=Function[{t,s},
	ParallelMap[First,Extract[EdgeRules[t["g"]],Position[EdgeRules[t["g"]],_->s]]]
];
(*Returns all the direct parents of s*)


FindG[t_,f_]:=
(*Find all G's*)
	Module[{for,minus={}},
		for=f[[0]][f[[1]],f[[2,1]]];(*formula without the G*)
		minus=Map[GetQminus,Map[Last,Values[t["hash"]]]];
		Map[VertexList[t["g"]][[#]]&,Map[#[[1]]&,Position[minus,for,2]]]
	];



AllGPath[t_,Q_]:=
(*Find all paths with G's*)
	Module[{aux,Q1,Gin,l={},i},
		Copy[Q,Q1];
		While[STpos[Q1,"Globally",False]!=0,
			Gin=STSubParts[Q1,"Globally",False];
			Gin=\!\(
\*SubscriptBox[\(@\), \(Gin[\([1]\)]\)]\([G\ Gin[\([2]\)]]\)\);
			aux=FindG[t,Gin];
			For[i = 1, i <= Length[VertexList[t["g"]]], i++,
					AppendTo[l,Map[FindPath[t["g"],PrintST[Q],#,{i},All]&,aux]]
			];
			RemoveQminus[Q1,Gin];
		];
		l
];


c3=Function[{t,Q},
	Module[{i,j,k,b,bb,a},
		a=AllGPath[t,Q];
		i=1;
		b=False;
		While[i<=Length[a]&&!b,
			j=1;
			While[j<=Length[a[[i]]&&!b],
				k=1;
				bb=True;
				While[k<=Length[a[[i,j]]]&&bb,
					Scan[If[MemberQ[PrintST[a[[i,j,k]]],#],bb=True;Return[],bb=False]&,t["closed"]];
					k++;
				];
				If[bb,b=True, b=False];
				j++;
			];
			i++;
		];
		b
]];


FindF=Function[{t,f},
(*Find all concretizations of the F formula*)
		Module[{for,plus},
			for=f[[0]][f[[1]],f[[2,1]]];
			plus=Map[GetQplus,Map[Last,Values[t["hash"]]]];
			Map[VertexList[t["g"]][[#]]&,Map[#[[1]]&,Position[plus,for,2]]]
]];


AllFPath=Function[{t,Q},
(*Find all paths with F's*)
	Module[{aux,Q1,Fin,l={},ff,i},
		Copy[Q,Q1];
		While[STpos[Q1,"Eventually",True]!=0,
			Fin=STSubParts[Q1,"Eventually",True];
			Fin=\!\(
\*SubscriptBox[\(@\), \(Fin[\([1]\)]\)]\([F\ Fin[\([2]\)]]\)\);
			aux=FindF[t,Fin];
			For[i = 1, i <= Length[VertexList[t["g"]]], i++,
					AppendTo[l,Map[FindPath[t["g"],PrintST[Q],#,{i},All]&,aux]]
			];
			RemoveQplus[Q1,Fin];
		];
		l
]];


c5=Function[{t,Q},
	Module[{i,j,k,b,bb,a},
		a=AllFPath[t,Q];
		i=1;
		b=False;
		While[i<=Length[a]&&!b,
			j=1;
			While[j<=Length[a[[i]]&&!b],
				k=1;
				bb=True;
				While[k<=Length[a[[i,j]]]&&bb,
					Scan[If[MemberQ[PrintST[a[[i,j,k]]],#],bb=True;Return[],bb=False]&,t["closed"]];
					k++;
				];
				If[bb,b=True,b=False];
				j++;
			];
			i++;
		];
		b
]];


FindU=Function[{t,f},
(*Find all F's*)
	Module[{for,plus},
		for=f[[0]][f[[1]],f[[2,2]]];
		plus=Map[GetQplus,Map[Last,Values[t["hash"]]]];
		Map[VertexList[t["g"]][[#]]&,Map[#[[1]]&,Position[plus,for,2]]]
]];


AllUPath=Function[{t,Q},
(*Find all paths with G's*)
	Module[{aux,Q1,Uin,l={},i},
		Copy[Q,Q1];
		While[STpos[Q1,"Until",True]!=0,
			Uin=STSubParts[Q1,"Until",True];
			Uin=\!\(
\*SubscriptBox[\(@\), \(Uin[\([1]\)]\)]\([Uin[\([2]\)]\ \[GothicCapitalU]\ Uin[\([3]\)]]\)\);
			aux=FindU[t,Uin];
			For[i = 1, i <= Length[VertexList[t["g"]]], i++,
					AppendTo[l,Map[FindPath[t["g"],PrintST[Q],#,{i},All]&,aux]]
			];
			RemoveQplus[Q1,Uin];
		];
		l
]];


c6=Function[{t,Q},
	Module[{i,j,k,b,bb,a},
		a=AllUPath[t,Q];
		i=1;
		b=False;
		While[i<=Length[a]&&!b,
			j=1;
			While[j<=Length[a[[i]]&&!b],
				k=1;
				bb=True;
				While[k<=Length[a[[i,j]]]&&bb,
					Scan[If[MemberQ[PrintST[a[[i,j,k]]],#],bb=True;Return[],bb=False]&,t["closed"]];
					k++;
				];
				If[bb,b=True,b=False];
				j++;
			];
			i++;
		];
		Remove[i,j,k,bb,a];
		b
]];


NotClosed=Function[{t},
	Select[VertexList[t["g"]],!MemberQ[t["closed"],#]&]
];
(*Set of nodes that are not closed*)


GetId=Function[{t},
	t["id"]
];
(*Universe of agents identifiers*)


Legend=Function[{t},
(*Legend of the graph*)
	Module[{i},
		Table[Print[i->PrintST[Values[t["hash"]][[i,2]]]],{i,Length[t["hash"]]}];
	]
];


End[];
EndPackage[];
