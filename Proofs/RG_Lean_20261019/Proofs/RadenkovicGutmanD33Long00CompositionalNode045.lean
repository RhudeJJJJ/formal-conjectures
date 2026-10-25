/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode044
import Proofs.RadenkovicGutmanD33Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,33]],[[0,0],[0,0]],[[-297,297],[297,2]],[[0,0],[0]],[[81,810],[810]],[[0,0],[0]],[[5517,774],[774]],[[0,0],[0]],[[17296,308],[308]],[[0,0],[0]],[[25976,49],[49]],[[0,0],[0]],[[22500,2],[2]],[[0]],[[11799]],[[0]],[[3740]],[[0]],[[683]],[[0]],[[63]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
