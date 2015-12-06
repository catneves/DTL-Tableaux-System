(* ::Package:: *)

BeginPackage["Cut`",{"StateTuple`","Tableau`","Theta`","Path`"}];

ContradictQ::usage="ContradictQ[c] returns True if c is contradictory and False otherwise";
Substitute::usage="Substitute[D,Dk,Q] returns the substituition in D of Dk by Q. D[\!\(\*SubscriptBox[\(D\), \(k\)]\):=Q] ";

GetStates::usage="GetStates[c]";
GetThetas::usage="GetThetas[c]";

GetState::usage="GetState[c,i]";
GetTheta::usage="GetTheta[c,i]";

C\[CapitalPi]::usage="C\[CapitalPi][ident,p] returns the set C\[CapitalPi] for each id presents the pair <Q,tetha>";
CQ::usage="CQ[t,Q] set of all the C\[CapitalPi]";

CutCopy::usage="CutCopy[C] makes a copy of the cut C";
FindState::usage="FindState[C,i] finds the state for each i bla in the cut C";


SetAttributes[{FindState,CutCopy,CQ,C\[CapitalPi],GetTheta,GetThetas,
GetState,GetStates,Substitute,ContradictQ,ExtendedC\[CapitalPi]},ReadProtected];


Begin["`Private`"];
ContradictQ=Function[{c},
	Module[{list,res},
	(*D is contradictory if there is a contradictory Di.
		D is of the form {Di,Di+1,...}
		Di is of the form <Q', Theta>*)
	list=Map[First,c];
	Scan[If[ContradictoryQ[#],res=True;Return[],res=False]&,list];
	Remove[list];
	res
]];


Substitute=Function[{D,Dk,Q},
	Replace[D,Dk->Q,{2}]
];


GetStates=Function[c,Map[First,c]];
GetThetas=Function[c,Map[Last,c]];


GetState=Function[{c,i},c[[i,1]]];
GetTheta=Function[{c,i},c[[i,2]]];


C\[CapitalPi]=Function[{ids,p},
	Module[{ident,res,i,j,Q,t},
		ident=ids;
		res={};
		i=1;
		While[ident!={},
			Q=p[[theta[p,First[ident]]]];
			t=Theta[ids,p,First[ident]];
			AppendTo[res,{Q,t}];
			ident=Complement[ident,t]
		];
		res	
]];


ExtendedC\[CapitalPi]=Function[{ids,p},
(*C\[CapitalPi] with the cut and the path correspondent*)
	{C\[CapitalPi][ids,p],p}
];


CQ=Function[{t,Q},
	Module[{res,P,p={},identi,i=1,and},
		identi=GetId[t];
		P=Paths[t,Q];
		While[i<=Length[P],
			p=Union[p,{StatePath[t,P[[i]]]}];
			i++
		];
		Scan[If[({}==#),and=True,and=False;Return[]]&,p];
		If[and,
(*Only to non paths. For empty paths return {}*)
			res={},
			res=Map[ExtendedC\[CapitalPi][identi,#]&,p]
		];
		res
]];


CutCopy=Function[{t,cut},
	Module[{Q,i=1,res={},C,path},
		C=cut[[1]];
		path=cut[[2]];
		For[i=1,i<=Length[C],i++,
			AppendTo[res,{State[t,C[[i,1]]],C[[i,2]]}]
		];
		{res,path}
]];


FindState=Function[{C,id},
	Module[{index},
		index=Flatten[Position[Map[Last,C], id]][[1]];
		C[[index,1]]
]];


End[];
EndPackage[];
