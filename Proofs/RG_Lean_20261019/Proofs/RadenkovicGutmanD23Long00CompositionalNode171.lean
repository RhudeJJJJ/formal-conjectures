/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode030
import Proofs.RadenkovicGutmanD23Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[46],[0]],[[0,0],[0]],[[690,0],[0]],[[0,0],[0]],[[4324,0],[0]],[[0,0],[0]],[[14674,0],[0]],[[0,0],[0]],[[29256,0],[0]],[[0,0],[0]],[[34822,23],[23]],[[0,0],[0]],[[24012,161],[161]],[[0,0],[0]],[[8694,368],[368]],[[0,0],[0]],[[1242,299],[299]],[[0,0],[0]],[[0,69],[69]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
