(* ::Package:: *)

BeginPackage["Formulas`",{"Notation`"}];
(*Definition of the operators @, \[Copyright], F, G, U e X. 
All the propositional symbols must be written as strings.
When applying an operator to a compound formula one should wrapp it in brackets.
For easier reading one can use [ ] to do it. When dealing with propositions or literals 
one can just leave a space between the operator and the formula.


For the binary operator U, one can writte (formula1) U (formula 2).
*)
Notation[ParsedBoxWrapper[RowBox[{"G", " ", "x_"}]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"G", "[", "x_", "]"}]]]
Notation[ParsedBoxWrapper[RowBox[{"X", " ", "x_"}]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"X", "[", "x_", "]"}]]]
Notation[ParsedBoxWrapper[RowBox[{SubscriptBox["@", "i_"], RowBox[{"[", "x_", "]"}]}]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"A", "[", RowBox[{"i_", ",", "x_"}], "]"}]]]
Notation[ParsedBoxWrapper[RowBox[{SubscriptBox["\[Copyright]", "j_"], "[", "x_", "]"}]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"CC", "[", RowBox[{"j_", ",", "x_"}], "]"}]]]
Notation[ParsedBoxWrapper[RowBox[{"F", " ", "x_"}]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"F", "[", "x_", "]"}]]] 
Notation[ParsedBoxWrapper[RowBox[{"x_", " ", "\[GothicCapitalU]", " ", "y_"}]] \[DoubleLongLeftRightArrow] ParsedBoxWrapper[RowBox[{"UU", "[", "x_", ",", "y_", "]"}]]]


Protect[G,X,A,CC,F,UU,\[Copyright],\[GothicCapitalU]];


FormulaQ::usage="FormulaQ[f] returns True if f is a well defined formula and False otherwise.";
FormulaType::usage="FormulaType[f] returns the type of the formula f, withouth disclosing the implementation details.
Possible Outputs: 
	GlobalBoolean, GlobalImplication, GlobalDisjunction, GlobalNegation, GlobalConjunction, GlobalEquivalence, 
	Boolean, Implication, Globally, Eventually, Next, Until, Negation, Disjunction, Conjunction, Communication, Proposition, Equivalence.
(Assumes f well-formed formula)";

AtomicGlobalQ::usage="AtomicGlobalQ[f] returns True if f is an atomic global formula and False otherwise.
(Assumes f well-formed formula)";
AtomicQ::usage="AtomicQ[f] returns True if f is an atomic formula and False otherwise.
(Assumes f well-formed formula)";

StateFormulaQ::usage="StateFormulaQ[f] returns True if f is a state formula and False otherwise.
(Assumes f well-formed formula)";

Ident::usage="Ident[f] returns the identifiers of the formula f, withouth disclosing the implementation details.
(Assumes f well-formed formula)";

SubParts::usages="SubParts[f,type] returns the subparts of the formula f, depending on its type.
(Assumes f well-formed formula and correct type)";


Begin["`Private`"];


SetAttributes[{FormulaType,SubParts,FormulaQ,LocalFormulaQ,
				AtomicGlobalQ,AtomicQ,StateFormulaQ,Ident},ReadProtected];


FormulaType=Function[{f},
(*returns the type of the formula withouth disclosing the implementation details*)
	Which[
		BooleanQ[f],
			"GlobalBoolean",
		Head[f]===Implies,
			"GlobalImplication",
		Head[f]===Or,
			"GlobalDisjunction",
		Head[f]===Not,
			"GlobalNegation",
		Head[f]===And,
			"GlobalConjunction",
		Head[f]===Equivalent,
			"GlobalEquivalence",
		Head[f]===A&&BooleanQ[f[[2]]],
			"Boolean",
		Head[f]===A&&Head[f[[2]]]===Implies,
			"Implication",
		Head[f]===A&&Head[f[[2]]]===G,
			"Globally",
		Head[f]===A&&Head[f[[2]]]===F,
			"Eventually",
		Head[f]===A&&Head[f[[2]]]===X,
			"Next",
		Head[f]===A&&Head[f[[2]]]===UU,
			"Until",
		Head[f]===A&&Head[f[[2]]]===Not,
			"Negation",
		Head[f]===A&&Head[f[[2]]]===Or,
			"Disjunction",
		Head[f]===A&&Head[f[[2]]]===And,
			"Conjunction",
		Head[f]===A&&Head[f[[2]]]===CC,
			"Communication",
		Head[f]===A&&Head[f[[2]]]===String,
			"Proposition",
		Head[f]===A&&Head[f[[2]]]===Equivalent,
			"Equivalence"
	]
];


SubParts=Function[{form,type},
(*SubParts of the formula f, depending on its type, without disclosing the implementation details*)
	Which[
		type=="GlobalNegation",
			{form[[1]]},		
		type=="GlobalImplication"||type=="GlobalDisjunction"||type=="GlobalConjunction"||type=="GlobalEquivalence"||type=="Proposition",
			{form[[1]],form[[2]]},
		type=="Globally"||type=="Eventually"||type=="Next"||type=="Negation",
			{form[[1]],form[[2,1]]},
		type=="Implication"||type=="Until"||type=="Disjunction"||type=="Conjunction"||type=="Communication"||type=="Equivalence",
			{form[[1]],form[[2,1]],form[[2,2]]},
		type=="GlobalBoolean"||type=="Boolean",
				{},
		type=="BooleanQ", (*only used to check which is the boolean*)
			{form[[2]]}
	]
];


FormulaQ=Function[{form},
(*Definition 3.2*)
	Which[
		BooleanQ[form],True, (*True or False*)
		Head[form]===Not,FormulaQ[Not[form]], (*global negation*)
		Head[form]===Or,FormulaQ[form[[1]]]&&FormulaQ[form[[2]]], (*global disjunction*)
		Head[form]===And,FormulaQ[form[[1]]]&&FormulaQ[form[[2]]], (*global conjunction*)
		Head[form]===Implies,FormulaQ[form[[1]]]&&FormulaQ[form[[2]]], (*global implication*)
		Head[form]===Equivalent,FormulaQ[form[[1]]]&&FormulaQ[form[[2]]], (*global equivalence*)
		Head[form]===A,LocalFormulaQ[form[[2]]], (*local formulas*)
		True, False
	]
];


LocalFormulaQ=Function[{form},
(*Definition 3.3*)
	Which[
		BooleanQ[form],True, (*local True or False*)
		Head[form]===String,True, (*Proposition*)				
		Head[form]===Not,LocalFormulaQ[Not[form]], (*local negation*)
		Head[form]===Or,LocalFormulaQ[form[[1]]]&&LocalFormulaQ[form[[2]]], (*local disjunction*)
		Head[form]===And,LocalFormulaQ[form[[1]]]&&LocalFormulaQ[form[[2]]], (*local conjunction*)
		Head[form]===Implies,LocalFormulaQ[form[[1]]]&&LocalFormulaQ[form[[2]]], (*local implication*)
		Head[form]===Equivalent,LocalFormulaQ[form[[1]]]&&LocalFormulaQ[form[[2]]], (*local equivalence*)
		Head[form]===X,LocalFormulaQ[form[[1]]], (*next formula*)
		Head[form]===CC,LocalFormulaQ[form[[2]]], (*communication formula*)
		Head[form]===G,LocalFormulaQ[form[[1]]], (*always formula*)
		Head[form]===F,LocalFormulaQ[form[[1]]], (*sometime formula*)
		Head[form]===UU,LocalFormulaQ[form[[1]]]&&LocalFormulaQ[form[[2]]], (*until formula*)
		True, False
		]
];


AtomicGlobalQ=Function[{form},
(*Definition 3.6*)
	Which[
		BooleanQ[form],True,
		Head[form]===A,True,				
		True, False
	]
];


AtomicQ=Function[{form},
(*Definition 3.5*)
	Which[
		BooleanQ[form],True, 
		Head[form]===A&&BooleanQ[form[[2]]],True,
		Head[form]===A&&Head[form[[2]]]===String,True, (*Porposition*)
		True, False
	]
];


StateFormulaQ=Function[{form},
(*Definition 3.7*)
	Which[
		AtomicQ[form],True,
		Head[form]===A,Head[form[[2]]]===X,
		True, False	
	]
];


Ident=Function[{f,list},
(*Recursive extraction of the agents identifiers of the formula f*)
	Module[{type},
		type=FormulaType[f];
		Which[
		(type=="GlobalBoolean"),
			list,
		(type=="Proposition"||type=="Boolean"),
			Union[list,{f[[1]]}],
		type=="GlobalNegation",
			Ident[f[[1]],list],
		(type=="GlobalImplication"
		||
		type=="GlobalDisjunction"
		||
		type=="GlobalConjunction"
		||
		type=="GlobalEquivalence"),
			Ident[f[[2]],Ident[f[[1]],list]],
		(type=="Implication"
		||
		type=="Until"
		||
		type=="Disjunction"
		||
		type=="Conjunction"
		||
		type=="Equivalence"
		),
			Ident[A[f[[1]],f[[2,1]]],Ident[A[f[[1]],f[[2,2]]],list]],
		(type=="Globally"
		||
		type=="Eventually"
		||
		type=="Next"
		||
		type=="Negation"		
		),
			Ident[A[f[[1]],f[[2,1]]],list],
		type=="Communication",
			Ident[A[f[[1]],f[[2,2]]],Union[list,{f[[2,1]]}]]
		]
]];


End[];
EndPackage[]
