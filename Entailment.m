(* ::Package:: *)

BeginPackage["Entailment`",{"Formulas`","StateTuple`","Rules`","AuxiliaryFunctions`","Cut`","Tableau`","Path`"}];
Construct::usage="Construct[t,p,id] returns an interpretation structure based on the tableau t, the path p and the identifiers id.";



Begin["`Private`"];


SetAttributes[{Construct,EventQ,Valuation},ReadProtected];


Construct=Function[{t,path,ident},
	Module[{mu,xi,lambda,st,i,v},
		st=1;
		lambda=Array[{}&,Length[ident]];
		xi=Array[{}&,Length[ident]];
		v=Table[Array[{}&,Length[path]],{Length[ident]}];
		While[st<=Length[path],
			i=1;
			While[i<=Length[ident],
				If[EventQ[t,path[[st]],ident[[i]]],
					AppendTo[lambda[[i]],path[[st]]];(*Add i to lambda;*)
					AppendTo[xi[[i]],st];(*Refresh the xi i;*)
					v=Valuation[t,v,xi[[i]],path[[st]],i](*Refresh the vi;*);
				];
				i++;
			];
			st++;
		];
(*Adjust the size of v*)
		i=1;
		While[i<=Length[ident],
			v[[i]]=Drop[v[[i]],Length[xi[[i]]]-Length[v[[i]]]];
			i++
		];
		mu={lambda,v};
		{mu,xi}
]];


Valuation=Function[{t,v,xi,s,i},
		Module[{st,vi,p,Q},
			Copy[State[t,s],Q];
			st=Length[xi];
			vi=v;
			While[STSubParts[Q,"Proposition",True]!={}||STSubParts[Q,"Proposition",False]!={},
				Which[
					STSubParts[Q,"Proposition",True]!={},
						p=STSubParts[Q,"Proposition",True];
						AppendTo[vi[[i,st]],p[[2]]];
						RemoveQplus[Q,\!\(
\*SubscriptBox[\(@\), \(p[\([1]\)]\)]\([p[\([2]\)]]\)\)],
					STSubParts[Q,"Proposition",False]!={},
						p=STSubParts[Q,"Proposition",False];
						AppendTo[vi[[i,st]],Not[p[[2]]]];
						RemoveQminus[Q,\!\(
\*SubscriptBox[\(@\), \(p[\([1]\)]\)]\([p[\([2]\)]]\)\)]
				]
			];
		vi
]];


EventQ=Function[{t,state,id},
		MemberQ[GetQX[State[t,state]],id]
];


End[];
EndPackage[];
