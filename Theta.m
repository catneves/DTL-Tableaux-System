(* ::Package:: *)

BeginPackage["Theta`",{"StateTuple`","Tableau`","Path`"}];

theta::usage="theta[p,i] identifies the StateTuple with bigger index where i is in QX, that is synchronized last.
If agent i had never synchronized, returns 1.";
Theta::usage="Theta[ident,p,i] finds all the other agents that also synchronized last in the same state that i did.";


Begin["`Private`"];


SetAttributes[{theta,Theta},ReadProtected];


theta=Function[{p,i},
	Module[{n,Xis},
		Xis=Map[GetQX,p];	
		n=Length[p];
		While[n>=2,
			If[MemberQ[Xis[[n]],i],
				Break[], (*last state where it synchorinezed*)
				n--
			];
		];
		n	(*min=1*)
]];
Theta=Function[{ident,p,i},
(*Pratition based on the agents identifiers*)
	Module[{t,j,iden,res},
		iden=Complement[ident,{i}];
		t=theta[p,i];
		res={i};
		j=1;
		While[j<=Length[iden],
(*share same prpoperty*)
			If[t==theta[p,iden[[j]]],
				AppendTo[res,iden[[j]]]
			];
			j++;
		];
		Sort[res]
]];

End[];
EndPackage[];
