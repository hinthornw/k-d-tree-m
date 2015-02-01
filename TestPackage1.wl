(* ::Package:: *)

BeginPackage["TestPackage1`"]


testFunc1::usage = "testFunc1[m_Integer, n_Integer]";


Begin["`Private`"]


testFunc1[
	m_Integer /; (m > 0),
	n_Integer /; (n >= 0)
] := m + 2 * n;
testFunc1[
	m_Integer,
	n_Integer
] := m + n;


End[]


EndPackage[]



