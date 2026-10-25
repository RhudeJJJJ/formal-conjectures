/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode204
import Proofs.RadenkovicGutmanD35Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[70,0],[0]],[[0,0],[0]],[[1120,0],[0]],[[0,0],[0]],[[7490,0],[0]],[[0,0],[0]],[[27160,0],[0]],[[0,0],[0]],[[57960,0],[0]],[[0,0],[0]],[[73920,70],[70]],[[0,0],[0]],[[54530,490],[490]],[[0,0],[0]],[[21000,1120],[1120]],[[0,0],[0]],[[3150,910],[910]],[[0,0],[0]],[[0,210],[210]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
