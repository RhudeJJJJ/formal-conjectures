/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode194
import Proofs.RadenkovicGutmanD22Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[88],[0]],[[0,0],[0]],[[1320,0],[0]],[[0,0],[0]],[[8272,0],[0]],[[0,0],[0]],[[28072,0],[0]],[[0,0],[0]],[[55968,0],[0]],[[0,0],[0]],[[66616,44],[44]],[[0,0],[0]],[[45936,308],[308]],[[0,0],[0]],[[16632,704],[704]],[[0,0],[0]],[[2376,572],[572]],[[0,0],[0]],[[0,132],[132]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
