/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode042
import Proofs.RadenkovicGutmanD2Long00CompositionalNode059
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e065 : NestedArithmetic.Expr 3 := .times e042 e059
noncomputable def p065 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,36],[0,72,0],[36,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,1620,312],[1620,624,0],[312,0]],[[0,0,0],[0,0,0],[0,0]],[[16200,18900,1060],[18900,2120,0],[1060,0]],[[0,0,0],[0,0,0],[0,0]],[[232200,94716,1832],[94716,3664,0],[1832,0]],[[0,0,0],[0,0,0],[0,0]],[[1487160,269880,1776],[269880,3552,0],[1776,0]],[[0,0,0],[0,0,0],[0,0]],[[5657280,488188,1000],[488188,2000,0],[1000,0]],[[0,0,0],[0,0],[0]],[[14332544,592276,324],[592276,648],[324]],[[0,0,0],[0,0],[0]],[[25690832,495632,56],[495632,112],[56]],[[0,0,0],[0,0],[0]],[[33766680,289212,4],[289212,8],[4]],[[0,0,0],[0,0],[0]],[[33257080,117236,0],[117236,0],[0]],[[0,0,0],[0,0],[0]],[[24851584,32328,0],[32328,0],[0]],[[0,0],[0]],[[14162920,5780],[5780]],[[0,0],[0]],[[6146984,604],[604]],[[0,0],[0]],[[2014320,28],[28]],[[0,0],[0]],[[489504,0],[0]],[[0,0],[0]],[[85440,0],[0]],[[0]],[[10120]],[[0]],[[728]],[[0]],[[24]],[[0]],[[0]],[[0]],[[0]]]
theorem step065 : p065=NestedArithmetic.mul p042 p059 := by decide +kernel
#print axioms step065
theorem h065 : NestedArithmetic.compile e065=p065 := StagedExprCompile.compile_times e065 e042 e059 p042 p059 p065 rfl h042 h059 step065
#print axioms h065
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
