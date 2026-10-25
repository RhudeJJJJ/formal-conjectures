/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode191
import Proofs.RadenkovicGutmanD33Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[63,0],[0,0]],[[0,0],[0,0]],[[683,0],[0,0]],[[0,0],[0,0]],[[3740,0],[0,0]],[[0,0],[0,0]],[[11799,0],[0,0]],[[0,0],[0,0]],[[22500,2],[2,0]],[[0,0],[0,0]],[[25976,49],[49,0]],[[0,0],[0,0]],[[17296,308],[308,0]],[[0,0],[0,0]],[[5517,774],[774,0]],[[0,0],[0,0]],[[81,810],[810,0]],[[0,0],[0,0]],[[-297,297],[297,2]],[[0],[0,0]],[[0],[0,33]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
