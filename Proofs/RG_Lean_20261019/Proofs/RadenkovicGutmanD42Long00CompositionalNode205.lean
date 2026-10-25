/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode204
import Proofs.RadenkovicGutmanD42Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[84,0],[0]],[[0,0],[0]],[[1344,0],[0]],[[0,0],[0]],[[8988,0],[0]],[[0,0],[0]],[[32592,0],[0]],[[0,0],[0]],[[69552,0],[0]],[[0,0],[0]],[[88704,84],[84]],[[0,0],[0]],[[65436,588],[588]],[[0,0],[0]],[[25200,1344],[1344]],[[0,0],[0]],[[3780,1092],[1092]],[[0,0],[0]],[[0,252],[252]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
