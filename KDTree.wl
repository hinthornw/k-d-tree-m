(* ::Package:: *)

BeginPackage["KDTree`"]


genRandomList::usage = "genRandomList[d_Integer, nV_Integer, xV_Integer]";
buildKDTree::usage = "buildKDTree[d_Integer, vL_List]";
getBestMatch::usage = "getBestMatch[kDT_List, tV_List]";
getBestMatchByLinearScanning::usage = "getBestMatchByLinearScanning[vL_List, tV_List]";
genRandomVec::usage = "genRandomVec[d_Integer, xV_Integer]";


Begin["`Private`"]


(* Generate a random list of n vectors of dimension d *)
genRandomList[
	d_Integer /; (d > 0),
	nV_Integer /; (nV > 0),
	xV_Integer /; (xV > 0)
] := Table[RandomInteger[xV],{i, 1, nV}, {j, 1, d}];
genRandomList[d_Integer, nV_Integer, xV_Integer] := {};


(* Build a k-d tree from a list of vectors *)
buildKDTree[
	d_Integer /; (d > 0),
	vL_List /; ((vL // Length) > 0)
] := Module[{cX, sVL, mI},
	cX = 1 + Mod[d - 1, Length[vL[[1]]]];
	sVL = Sort[vL, (#1[[cX]] < #2[[cX]] &)];
	mI = 1 + Floor[Length[sVL] / 2.];
	{
		sVL[[mI]],
		buildKDTree[d + 1, sVL[[;;(mI - 1)]]],
		buildKDTree[d + 1, sVL[[(mI + 1);;]]]
	}
];
buildKDTree[d_Integer, rL_List] := {};


(* Traverse along a path *)
traverseKDTree[
	cKDT : {{__Integer}, _List, _List},
	cP_List /; ((cP//Length) > 0)
] := traverseKDTree[cKDT[[cP[[1]] + 1]], cP[[2;;]]];
traverseKDTree[cKDT_List, cP_List] := cKDT;


(* Distance-square function *)
distSq := Composition[Total, (#^2&), Subtract];


(* Get the candidate best match *)
getCandBestMatch[
	cKDT_List /; MatchQ[cKDT, {{__Integer}, _List, _List}],
	tV_List /; ((tV // Length) > 0),
	cD_Integer /; (cD > 0),
	pA_List
] := Module[{cX, lFs},
	cX = 1 + Mod[cD - 1, Length[tV]];
	lFs = (MatchQ[cKDT[[# ]], {{__Integer}, _List, _List}] &) /@ {2, 3};
	If[tV[[cX]] < cKDT[[1]][[cX]],
		If[lFs[[1]],
			getCandBestMatch[cKDT[[2]], tV, cD + 1, Join[{cKDT}, pA]],
			If[lFs[[2]],
				getCandBestMatch[cKDT[[3]], tV, cD + 1, Join[{cKDT}, pA]],
				checkCandBestMatch[cKDT, distSq[tV, cKDT[[1]]], tV, pA, cD]
			]
		],
		If[lFs[[2]],
			getCandBestMatch[cKDT[[3]], tV, cD + 1, Join[{cKDT}, pA]],
			If[lFs[[1]],
				getCandBestMatch[cKDT[[2]], tV, cD + 1, Join[{cKDT}, pA]],
				checkCandBestMatch[cKDT, distSq[tV, cKDT[[1]]], tV, pA, cD]
			]
		]
	]
];
getCandBestMatch[cKDT_List, tV_List, cD_Integer, pA_List] := {{}, pA, cD};


(* Check the candidate best match *)
checkCandBestMatch[
	cBM_List /; MatchQ[cBM, {{__Integer}, _List, _List}],
	cBMD_Integer,
	tV_List,
	pA_List /; !MatchQ[pA, {}],
	cD_Integer
] := Module[{pD, cX, pX, pSD, pSDSq, hCBM, hCBMD},
	pD = distSq[tV, pA[[1, 1]]];
	cX = 1 + Mod[cD - 1, Length[tV]];
	pX = If[cX == 1, Length @ tV, cX - 1];
	pSD = tV[[pX]] - pA[[1, 1, pX]];
	pSDSq = pSD * pSD;
	If[cBMD <= pD,
		If[pSDSq < cBMD,
			hCBM = getCandBestMatch[pA[[1, If[pSD < 0, 3, 2]]], tV, cD, {}];
			If[
				MatchQ[hCBM[[1]], {{__Integer}, _List, _List}] &&
				CompoundExpression[hCBMD = distSq[hCBM[[1, 1]], tV], hCBMD] < cBMD,
				checkCandBestMatch[hCBM[[1]], hCBMD, tV, pA[[2;;]], cD - 1],
				checkCandBestMatch[cBM, cBMD, tV, pA[[2;;]], cD - 1]
			],
			checkCandBestMatch[cBM,cBMD,tV,pA[[2;;]],cD-1]
		],
		If[pSDSq < pD,
			hCBM = getCandBestMatch[pA[[1, If[pSD < 0, 3, 2]]], tV, cD, {}];
			If[
				MatchQ[hCBM[[1]], {{__Integer}, _List, _List}] &&
				CompoundExpression[hCBMD = distSq[hCBM[[1, 1]], tV], hCBMD] < pD,
				checkCandBestMatch[hCBM[[1]], hCBMD, tV, pA[[2;;]], cD - 1],
				checkCandBestMatch[pA[[1]], pD, tV, pA[[2;;]], cD - 1]
			],
			checkCandBestMatch[pA[[1]], pD, tV, pA[[2;;]], cD - 1]
		]
	]
];
checkCandBestMatch[cBM_List, cBMD_Integer, tV_List, pA_List, cD_Integer] := {cBM, pA, cD};


(* Get the best match *)
getBestMatch[kDT_List, tV_List] := getCandBestMatch[kDT, tV, 1, {}];


(* Get the best match by scanning linearly *)
getBestMatchByLinearScanning[vL_List, tV_List] :=
	Fold[If[distSq[#1, tV] < distSq[#2, tV], #1, #2] &, First @ vL, Rest @ vL];


(* Generate a random test vector *)
genRandomVec[d_Integer, xV_Integer] := genRandomList[d, 1, xV][[1]];


End[]


EndPackage[]



