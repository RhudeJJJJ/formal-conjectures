/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode030
import Proofs.RadenkovicGutmanD16Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[32],[0]],[[0,0],[0]],[[480,0],[0]],[[0,0],[0]],[[3008,0],[0]],[[0,0],[0]],[[10208,0],[0]],[[0,0],[0]],[[20352,0],[0]],[[0,0],[0]],[[24224,16],[16]],[[0,0],[0]],[[16704,112],[112]],[[0,0],[0]],[[6048,256],[256]],[[0,0],[0]],[[864,208],[208]],[[0,0],[0]],[[0,48],[48]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
