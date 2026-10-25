/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode030
import Proofs.RadenkovicGutmanD13Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .times e030 e032
noncomputable def p033 : NestedHorner.Poly 3 := [[[0],[0,13]],[[0,0],[0]],[[-117,117],[117]],[[0,0],[0]],[[39,312],[312]],[[0,0],[0]],[[2171,286],[286]],[[0,0],[0]],[[6682,104],[104]],[[0,0],[0]],[[9828,13],[13]],[[0]],[[8268]],[[0]],[[4147]],[[0]],[[1222]],[[0]],[[195]],[[0]],[[13]]]
theorem step033 : p033=NestedArithmetic.mul p030 p032 := by decide +kernel
#print axioms step033
theorem h033 : NestedArithmetic.compile e033=p033 := StagedExprCompile.compile_times e033 e030 e032 p030 p032 p033 rfl h030 h032 step033
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
