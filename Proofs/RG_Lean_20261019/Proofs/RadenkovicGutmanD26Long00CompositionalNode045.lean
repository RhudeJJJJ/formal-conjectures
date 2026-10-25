/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode044
import Proofs.RadenkovicGutmanD26Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,26]],[[0,0],[0,0]],[[-234,234],[234,2]],[[0,0],[0]],[[60,642],[642]],[[0,0],[0]],[[4348,620],[620]],[[0,0],[0]],[[13698,252],[252]],[[0,0],[0]],[[20684,42],[42]],[[0,0],[0]],[[18048,2],[2]],[[0]],[[9566]],[[0]],[[3082]],[[0]],[[578]],[[0]],[[56]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
