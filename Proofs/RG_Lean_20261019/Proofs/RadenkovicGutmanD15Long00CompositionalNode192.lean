/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode191
import Proofs.RadenkovicGutmanD15Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[45,0],[0,0]],[[0,0],[0,0]],[[413,0],[0,0]],[[0,0],[0,0]],[[2048,0],[0,0]],[[0,0],[0,0]],[[6057,0],[0,0]],[[0,0],[0,0]],[[11052,2],[2,0]],[[0,0],[0,0]],[[12368,31],[31,0]],[[0,0],[0,0]],[[8044,164],[164,0]],[[0,0],[0,0]],[[2511,378],[378,0]],[[0,0],[0,0]],[[27,378],[378,0]],[[0,0],[0,0]],[[-135,135],[135,2]],[[0],[0,0]],[[0],[0,15]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
