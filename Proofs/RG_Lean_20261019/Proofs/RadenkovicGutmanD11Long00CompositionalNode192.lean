/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode191
import Proofs.RadenkovicGutmanD11Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[41,0],[0,0]],[[0,0],[0,0]],[[353,0],[0,0]],[[0,0],[0,0]],[[1672,0],[0,0]],[[0,0],[0,0]],[[4781,0],[0,0]],[[0,0],[0,0]],[[8508,2],[2,0]],[[0,0],[0,0]],[[9344,27],[27,0]],[[0,0],[0,0]],[[5988,132],[132,0]],[[0,0],[0,0]],[[1843,290],[290,0]],[[0,0],[0,0]],[[15,282],[282,0]],[[0,0],[0,0]],[[-99,99],[99,2]],[[0],[0,0]],[[0],[0,11]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
