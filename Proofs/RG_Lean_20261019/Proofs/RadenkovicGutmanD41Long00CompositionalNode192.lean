/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode191
import Proofs.RadenkovicGutmanD41Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[71,0],[0,0]],[[0,0],[0,0]],[[803,0],[0,0]],[[0,0],[0,0]],[[4492,0],[0,0]],[[0,0],[0,0]],[[14351,0],[0,0]],[[0,0],[0,0]],[[27588,2],[2,0]],[[0,0],[0,0]],[[32024,57],[57,0]],[[0,0],[0,0]],[[21408,372],[372,0]],[[0,0],[0,0]],[[6853,950],[950,0]],[[0,0],[0,0]],[[105,1002],[1002,0]],[[0,0],[0,0]],[[-369,369],[369,2]],[[0],[0,0]],[[0],[0,41]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
