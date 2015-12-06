(* ::Package:: *)

BeginPackage["Path`",{"StateTuple`","Tableau`"}];

Paths::usage="Paths[t,Q]";
path::usage="path[P,i] returns the i-th path of P";
StatePath::usage="StatePath[p] returns path p with only non-closed states ";



Begin["`Private`"];


SetAttributes[{Paths,path,StatePath},ReadProtected];


Paths=Function[{t,Q},
	(*Q: state and non closed*)
	Module[{l,i,j},
		l=FindPath[t["g"],First[VertexList[t["g"]]],Q,Infinity,All];
		i=1;
		While[i<=Length[l],
			(*If the path has a closed node, it is deleted*)
			If[Apply[Or,Map[ClosedQ[t,#]&, l[[i]]]],
				l=Delete[l,i],
				i++
			]
		];
		l
]];
path=Function[{P,i},
	If[i<=Length[P],
		P[[i]],
	Print["There is no such path"]
	]
];
StatePath=Function[{t,p},
(*Definitions 6.1 and 6.2*)
	Module[{l,states},
		(*Path with only states and non-closed ones*)
		states= Map[State[t,#]&,p];
		l=Map[StateQ,states];
		Pick[p,l]
]];


End[];
EndPackage[];
