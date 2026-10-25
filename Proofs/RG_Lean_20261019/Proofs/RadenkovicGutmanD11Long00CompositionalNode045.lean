/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode044
import Proofs.RadenkovicGutmanD11Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,11]],[[0,0],[0,0]],[[-99,99],[99,2]],[[0,0],[0]],[[15,282],[282]],[[0,0],[0]],[[1843,290],[290]],[[0,0],[0]],[[5988,132],[132]],[[0,0],[0]],[[9344,27],[27]],[[0,0],[0]],[[8508,2],[2]],[[0]],[[4781]],[[0]],[[1672]],[[0]],[[353]],[[0]],[[41]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
