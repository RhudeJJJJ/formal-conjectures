/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode192
import Proofs.RadenkovicGutmanD33Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[63,0],[0,0]],[[0,0],[0,0]],[[683,0],[0,0]],[[0,0],[0,0]],[[3740,0],[0,0]],[[0,0],[0,0]],[[11799,0],[0,0]],[[0,0],[0,0]],[[22500,2],[2,0]],[[0,0],[0,0]],[[25976,49],[49,0]],[[0,0],[0,0]],[[17296,308],[308,0]],[[0,0],[0,0]],[[5517,774],[774,0]],[[0,0],[0,0]],[[81,810],[810,0]],[[0,0],[0,0]],[[-297,297],[297,2]],[[0],[0,0]],[[0],[0,33]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
