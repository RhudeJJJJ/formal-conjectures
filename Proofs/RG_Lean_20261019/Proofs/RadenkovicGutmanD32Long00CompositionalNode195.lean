/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode194
import Proofs.RadenkovicGutmanD32Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[128],[0]],[[0,0],[0]],[[1920,0],[0]],[[0,0],[0]],[[12032,0],[0]],[[0,0],[0]],[[40832,0],[0]],[[0,0],[0]],[[81408,0],[0]],[[0,0],[0]],[[96896,64],[64]],[[0,0],[0]],[[66816,448],[448]],[[0,0],[0]],[[24192,1024],[1024]],[[0,0],[0]],[[3456,832],[832]],[[0,0],[0]],[[0,192],[192]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
