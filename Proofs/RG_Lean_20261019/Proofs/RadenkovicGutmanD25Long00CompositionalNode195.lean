/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode194
import Proofs.RadenkovicGutmanD25Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[100],[0]],[[0,0],[0]],[[1500,0],[0]],[[0,0],[0]],[[9400,0],[0]],[[0,0],[0]],[[31900,0],[0]],[[0,0],[0]],[[63600,0],[0]],[[0,0],[0]],[[75700,50],[50]],[[0,0],[0]],[[52200,350],[350]],[[0,0],[0]],[[18900,800],[800]],[[0,0],[0]],[[2700,650],[650]],[[0,0],[0]],[[0,150],[150]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
