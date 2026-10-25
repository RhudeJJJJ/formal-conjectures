/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode195
import Proofs.RadenkovicGutmanD8Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[32,0],[0]],[[0,0],[0]],[[480,0],[0]],[[0,0],[0]],[[3008,0],[0]],[[0,0],[0]],[[10208,0],[0]],[[0,0],[0]],[[20352,0],[0]],[[0,0],[0]],[[24224,16],[16]],[[0,0],[0]],[[16704,112],[112]],[[0,0],[0]],[[6048,256],[256]],[[0,0],[0]],[[864,208],[208]],[[0,0],[0]],[[0,48],[48]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
