/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode195
import Proofs.RadenkovicGutmanD35Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[140,0],[0]],[[0,0],[0]],[[2100,0],[0]],[[0,0],[0]],[[13160,0],[0]],[[0,0],[0]],[[44660,0],[0]],[[0,0],[0]],[[89040,0],[0]],[[0,0],[0]],[[105980,70],[70]],[[0,0],[0]],[[73080,490],[490]],[[0,0],[0]],[[26460,1120],[1120]],[[0,0],[0]],[[3780,910],[910]],[[0,0],[0]],[[0,210],[210]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
