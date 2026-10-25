/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode192
import Proofs.RadenkovicGutmanD11Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[41,0],[0,0]],[[0,0],[0,0]],[[353,0],[0,0]],[[0,0],[0,0]],[[1672,0],[0,0]],[[0,0],[0,0]],[[4781,0],[0,0]],[[0,0],[0,0]],[[8508,2],[2,0]],[[0,0],[0,0]],[[9344,27],[27,0]],[[0,0],[0,0]],[[5988,132],[132,0]],[[0,0],[0,0]],[[1843,290],[290,0]],[[0,0],[0,0]],[[15,282],[282,0]],[[0,0],[0,0]],[[-99,99],[99,2]],[[0],[0,0]],[[0],[0,11]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
