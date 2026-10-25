/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode194
import Proofs.RadenkovicGutmanD27Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[108],[0]],[[0,0],[0]],[[1620,0],[0]],[[0,0],[0]],[[10152,0],[0]],[[0,0],[0]],[[34452,0],[0]],[[0,0],[0]],[[68688,0],[0]],[[0,0],[0]],[[81756,54],[54]],[[0,0],[0]],[[56376,378],[378]],[[0,0],[0]],[[20412,864],[864]],[[0,0],[0]],[[2916,702],[702]],[[0,0],[0]],[[0,162],[162]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
