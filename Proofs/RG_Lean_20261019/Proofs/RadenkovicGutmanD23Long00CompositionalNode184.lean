/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode030
import Proofs.RadenkovicGutmanD23Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[23],[0]],[[0,0],[0]],[[368,0],[0]],[[0,0],[0]],[[2461,0],[0]],[[0,0],[0]],[[8924,0],[0]],[[0,0],[0]],[[19044,0],[0]],[[0,0],[0]],[[24288,23],[23]],[[0,0],[0]],[[17917,161],[161]],[[0,0],[0]],[[6900,368],[368]],[[0,0],[0]],[[1035,299],[299]],[[0,0],[0]],[[0,69],[69]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
