/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode194
import Proofs.RadenkovicGutmanD8Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[32],[0]],[[0,0],[0]],[[480,0],[0]],[[0,0],[0]],[[3008,0],[0]],[[0,0],[0]],[[10208,0],[0]],[[0,0],[0]],[[20352,0],[0]],[[0,0],[0]],[[24224,16],[16]],[[0,0],[0]],[[16704,112],[112]],[[0,0],[0]],[[6048,256],[256]],[[0,0],[0]],[[864,208],[208]],[[0,0],[0]],[[0,48],[48]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
