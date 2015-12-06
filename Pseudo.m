(* ::Package:: *)

BeginPackage["Pseudo`",{"Entailment`","Formulas`","StateTuple`","Rules`","AuxiliaryFunctions`","Cut`","Tableau`","Path`","Stack`"}];
Ent::usage="Ent[set,delta] is the algorithm for checking global invariants.";


Begin["`Private`"];


SetAttributes[{Ent,SetGlobal,LocSat},ReadProtected];


SetGlobal=Function[{t,cut,delta},
	Module[{R,S,P,delta0, delta1, delta2,D,l1,l2,i,id,Q,Q1,form},
		R={};
		S={};
		push[R,{{},{delta}}];
		While[!EmptyStackQ[R],
			P=pop[R];
			l1=Complement[P[[1]],Select[P[[1]],AtomicGlobalQ]];
			l2=Complement[P[[2]],Select[P[[2]],AtomicGlobalQ]];
			If[l1=={},
				If[l2=={},
					If[(!MemberQ[P[[1]],False])||(!MemberQ[P[[2]],True]),
						D=CutCopy[t,cut];
						For[i=1,i<=Length[P[[1]]],i++,
							form=P[[1,i]];
							If[AtomicGlobalQ[form]&&!TrueQ[!form]&&!TrueQ[form],
						(*for \!\(each\ 
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\) \in P[[1]], Union[Subscript[D, i][[1]],{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\)}]*)
								id=form[[1]];
								Q=FindState[D[[1]],id];
								Copy[Q,Q1];	
								InsertQplus[Q,form];
								D[[1]]=D[[1]]/.Q1->Q;
							];
						];
						For[i=1,i<=Length[P[[2]]],i++,
					(*for \!\(each\ 
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\) \in P[[2]], Union[Subscript[D, i][[2]],{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Phi]]\)\)}]*)
							form=P[[2,i]];
							If[AtomicGlobalQ[form]&&!TrueQ[!form]&&!TrueQ[form],
								id=form[[1]];
								Q=FindState[D[[1]],id];
								Copy[Q,Q1];	
								InsertQminus[Q,form];
								D[[1]]=D[[1]]/.Q1->Q;
							]
						];
						If[!ContradictQ[D[[1]]],push[S,D]]
					],
					delta0=First[l2];(*Let delta0 be the first non atomic global formula in P-*)
					Which[(*Which non atomic global formula is delta0?*)
						FormulaType[delta0]=="GlobalImplication",
							{delta1,delta2}=SubParts[delta0,"GlobalImplication"];
							push[R,{Union[P[[1]],{delta1}],Union[Complement[P[[2]],{delta0}],{delta2}]}],
						FormulaType[delta0]=="GlobalEquivalence",
							{delta1,delta2}=SubParts[delta0,"GlobalEquivalence"];
							push[R,{Union[P[[1]],{delta1}],Union[Complement[P[[2]],{delta0}],{delta2}]}];
							push[R,{Union[P[[1]],{delta2}],Union[Complement[P[[2]],{delta0}],{delta1}]}],
						FormulaType[delta0]=="GlobalConjunction",
							{delta1,delta2}=SubParts[delta0,"GlobalConjunction"];
							push[R,{P[[1]],Union[Complement[P[[2]],{delta0}],{delta1}]}];
							push[R,{P[[1]],Union[Complement[P[[2]],{delta0}],{delta2}]}],
						FormulaType[delta0]=="GlobalDisjunction",
							{delta1,delta2}=SubParts[delta0,"GlobalDisjunction"];
							push[R,{P[[1]],Union[Complement[P[[2]],{delta0}],{delta1,delta2}]}],
						FormulaType[delta0]=="GlobalNegation",
							push[R,{Union[P[[1]],{Not[delta0]}],Complement[P[[2]],{delta0}]}]
					];
				],
				delta0=First[l1];(*Let delta0 be the first non atomic global formula in P+*)
				Which[
					FormulaType[delta0]=="GlobalImplication",
						{delta1,delta2}=SubParts[delta0,"GlobalImplication"];
						push[R,{Complement[P[[1]],{delta0}],Union[P[[2]],{delta1}]}];
						push[R,{Union[Complement[P[[1]],{delta0}],{delta2}],P[[2]]}],
					FormulaType[delta0]=="GlobalEquivalence",
						{delta1,delta2}=SubParts[delta0,"GlobalEquivalence"];
						push[R,{P[[1]],Union[Complement[P[[2]],{delta0}],{delta1,delta2}]}];
						push[R,{Union[P[[1]],{delta1,delta2}],Complement[P[[2]],{delta0}]}],
					FormulaType[delta0]=="GlobalConjunction",
						{delta1,delta2}=SubParts[delta0,"GlobalConjunction"];
						push[R,{Union[Complement[P[[1]],{delta0}],{delta1,delta2}],P[[2]]}],
					FormulaType[delta0]=="GlobalDisjunction",
						{delta1,delta2}=SubParts[delta0,"GlobalDisjunction"];
						push[R,{Union[Complement[P[[1]],{delta0}],{delta1}],P[[2]]}];
						push[R,{Union[Complement[P[[1]],{delta0}],{delta2}],P[[2]]}],
					FormulaType[delta0]=="GlobalNegation",
						push[R,{Complement[P[[1]],{delta0}],Union[P[[2]],{Not[delta0]}]}]
				]
			]
		];
		S
	]
];


LocSat=Function[{t,cut,delta},
	Module[{ident,b,S,D,Dk,delta0,\[Psi]1,\[Psi]2,
			Q,dplus,dminus,dbow,d\[NumberSign],dX,
			aux,i,j,nonplus,nonminus},
		ident=Identifiers[State[t,cut[[2,1]]]];
		b=False;
		S=SetGlobal[t,cut,delta];
		While[!EmptyStackQ[S]&&!b,
			D=top[S];
			nonplus=False;
			nonminus=False;
			For[i=1,i<=Length[D[[1]]],i++,
				Dk=GetState[D[[1]],i];
				dplus=GetQplus[Dk];
				dminus=GetQminus[Dk];
				Which[
					!Apply[And,Map[StateFormulaQ,dplus]],
				(*if exists a formula non state formula in Q+*)
						nonplus=True;
						aux=Map[StateFormulaQ,dplus];
						delta0=Pick[dplus,aux,False][[1]];
						Break[],
					!Apply[And,Map[StateFormulaQ,dminus]],
				(*if in Q+ does not exist, and in Q- exist some formula that is non state formula*)
						nonminus=True;
						aux=Map[StateFormulaQ,dminus];
						delta0=Pick[dminus,aux,False][[1]];
						Break[]
				]
			];
			Which[
				nonplus(*some Dk with k \in Id contains a non state formula*),
					pop[S];			
					dbow=GetQbowtie[Dk];
					d\[NumberSign]=GetQ\[NumberSign][Dk];
					dX=GetQX[Dk];
					Which[
(*All the formulas formulas*)
						FormulaType[delta0]=="Implication",
							{i,\[Psi]1,\[Psi]2}=SubParts[delta0,"Implication"];
							aux=Complement[dplus,{delta0}];
							StateTuple[Q,aux,Union[dminus,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]1]\)\)}],dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]];
							StateTuple[Q,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]2]\)\)}],dminus,dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]],
						FormulaType[delta0]=="Negation",
							{i,\[Psi]1}=SubParts[delta0,"Negation"];
							aux=Complement[dplus,{delta0}];
							StateTuple[Q,aux,Union[dminus,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]1]\)\)}],dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]],
						FormulaType[delta0]=="Conjunction",
							{i,\[Psi]1,\[Psi]2}=SubParts[delta0,"Conjunction"];
							aux=Complement[dplus,{delta0}];
							StateTuple[Q,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]1]\)\),\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]2]\)\)}],dminus,dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]],
						FormulaType[delta0]=="Disjunction",
							{i,\[Psi]1,\[Psi]2}=SubParts[delta0,"Disjunction"];
							aux=Complement[dplus,{delta0}];
							StateTuple[Q,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]1]\)\)}],dminus,dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]];
							StateTuple[Q,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]2]\)\)}],dminus,dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]],
						FormulaType[delta0]=="Equivalence",
							{i,\[Psi]1,\[Psi]2}=SubParts[delta0,"Equivalence"];
							aux=Complement[dplus,{delta0}];
							StateTuple[Q,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]1]\)\),\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]2]\)\)}],dminus,dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]];
							StateTuple[Q,aux,Union[dminus,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]1]\)\),\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]2]\)\)}],dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]],
						FormulaType[delta0]=="Globally",
							{i,\[Psi]1}=SubParts[delta0,"Globally"];
							aux=Complement[dplus,{delta0}];
							StateTuple[Q,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]1]\)\),\!\(
\*SubscriptBox[\(@\), \(i\)]\([X[G[\[Psi]1]]]\)\)}],dminus,dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]],
						FormulaType[delta0]=="Eventually",
							{i,\[Psi]1}=SubParts[delta0,"Eventually"];
							aux=Complement[dplus,{delta0}];
							StateTuple[Q,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]1]\)\)}],dminus,dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]];
							StateTuple[Q,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([X[F[\[Psi]1]]]\)\)}],dminus,dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]],
						FormulaType[delta0]=="Until",
							{i,\[Psi]1,\[Psi]2}=SubParts[delta0,"Until"];
							aux=Complement[dplus,{delta0}];
							StateTuple[Q,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]2]\)\)}],dminus,dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]];
							StateTuple[Q,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]1]\)\),\!\(
\*SubscriptBox[\(@\), \(i\)]\([X[\[Psi]1\ U\ \[Psi]2]]\)\)}],dminus,dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]],
						FormulaType[delta0]=="Communication",			
							{i,j,\[Psi]1}=SubParts[delta0,"Communication"];
							aux=Complement[dplus,{delta0}];
							If[
								MemberQ[dX,j],			
								StateTuple[Q,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(j\)]\([\[Psi]1]\)\)}],dminus,dbow,d\[NumberSign],dX];
								If[!ContradictoryQ[Q],push[S,Substitute[D,Dk,Q]]]
							]
					],
				nonminus,
					pop[S];			
					dbow=GetQbowtie[Dk];
					d\[NumberSign]=GetQ\[NumberSign][Dk];
					dX=GetQX[Dk];
					Which[
					(*alterar isto do i e do j n pode ser assim!!!!*)
						FormulaType[delta0]=="Implication",
							{i,\[Psi]1,\[Psi]2}=SubParts[delta0,"Implication"];
							aux=Complement[dminus,{delta0}];
							StateTuple[Q,Union[dplus,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]1]\)\)}],Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]2]\)\)}],dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]],
						FormulaType[delta0]=="Negation",
							{i,\[Psi]1,\[Psi]2}=SubParts[delta0,"Negation"];
							aux=Complement[dminus,{delta0}];
							StateTuple[Q,Union[dplus,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]1]\)\)}],aux,dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]],
						FormulaType[delta0]=="Conjunction",
							{i,\[Psi]1,\[Psi]2}=SubParts[delta0,"Conjunction"];
							aux=Complement[dplus,{delta0}];
							StateTuple[Q,dplus,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]1]\)\)}],dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]];
							StateTuple[Q,dplus,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]2]\)\)}],dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]],
						FormulaType[delta0]=="Disjuction",
							{i,\[Psi]1,\[Psi]2}=SubParts[delta0,"Disjuction"];
							aux=Complement[dminus,{delta0}];
							StateTuple[Q,dplus,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]1]\)\),\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]2]\)\)}],dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]],
						FormulaType[delta0]=="Equivalence",
							{i,\[Psi]1,\[Psi]2}=SubParts[delta0,"Equivalence"];
							aux=Complement[dplus,{delta0}];
							StateTuple[Q,Union[dplus,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]1]\)\)}],Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]2]\)\)}],dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]];
							StateTuple[Q,Union[dplus,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]1]\)\)}],Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]2]\)\)}],dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]],
						FormulaType[delta0]=="Conjunction",
							{i,\[Psi]1,\[Psi]2}=SubParts[delta0,"Conjunction"];
							aux=Complement[dplus,{delta0}];
							StateTuple[Q,dplus,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]1]\)\)}],dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]];
							StateTuple[Q,dplus,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]2]\)\)}],dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]],
						FormulaType[delta0]=="Globally",
							{i,\[Psi]1}=SubParts[delta0,"Globally"];
							aux=Complement[dplus,{delta0}];
							StateTuple[Q,dplus,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]1]\)\)}],dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]];
							StateTuple[Q,dplus,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([X[G[\[Psi]1]]]\)\)}],dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]],
						FormulaType[delta0]=="Eventually",
							{i,\[Psi]1}=SubParts[delta0,"Eventually"];
							aux=Complement[dminus,{delta0}];
							StateTuple[Q,dplus,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]1]\)\),\!\(
\*SubscriptBox[\(@\), \(i\)]\([X[F[\[Psi]1]]]\)\)}],dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]],
						FormulaType[delta0]=="Until",
							{i,\[Psi]1,\[Psi]2}=SubParts[delta0,"Until"];
							aux=Complement[dplus,{delta0}];
							StateTuple[Q,dplus,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]1]\)\),\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]2]\)\)}],dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]];
							StateTuple[Q,dplus,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(i\)]\([\[Psi]2]\)\),\!\(
\*SubscriptBox[\(@\), \(i\)]\([X[\[Psi]1\ U\ \[Psi]2]]\)\)}],dbow,d\[NumberSign],dX];
							If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]],
						FormulaType[delta0]=="Communication",
							{i,j,\[Psi]1}=SubParts[delta0,"Communication"];
							aux=Complement[dminus,{dminus,delta0}];
							If[MemberQ[dX,j],
								StateTuple[Q,dplus,Union[aux,{\!\(
\*SubscriptBox[\(@\), \(j\)]\([\[Psi]1]\)\)}],dbow,d\[NumberSign],dX];
								If[!ContradictoryQ[Q],push[S,Substitute[D[[1]],Dk,Q]]],
								StateTuple[Q,dplus,aux,dbow,d\[NumberSign],dX];
								push[S,Substitute[D[[1]],Dk,Q]]
							]
					],
				True,
					b=True;
			]
		];
	If[b,
		aux=Construct[t,D[[2]],ident];(*top[S]*)
		aux={b,aux[[1]],aux[[2]]},
		aux={b,"_","_"}
	];
	aux
	]
];


Ent=Function[{set,delta},
Module[{Q0,t,Q,O,b,TQ,C,locSat,b1,miu,xi,a,time},
	Catch[
	NewStateTuple[Q0,set,{},{},{},{}];
	Tableau[t,Q0];
	Iterate[t];
(*Print[HighlightGraph[t["g"],t["closed"]]];*)
	If[!SuccessfulQ[t],
		Throw["yes "],
		O=NotClosed[t];
		b=False;
		While[O!={}&&!b,
			Q=Last[O];			
			O=Most[O];
			TQ=CQ[t,Q];
			While[TQ!={}&&!b,
				C=Last[TQ];
				TQ=Most[TQ];
				locSat=LocSat[t,C,delta];
				b1=locSat[[1]];
				miu=locSat[[2]];
				xi=locSat[[3]];
				b=b||b1
			]
		]
	];
	If[!b,
		Throw["yes"],
		Throw[{"no",miu,xi}]
	]
]
]
];


End[];
EndPackage[];
