/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode030
import Proofs.RadenkovicGutmanD13Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[13],[0]],[[0,0],[0]],[[195,0],[0,0]],[[0,0],[0,0]],[[1222,0],[0,0]],[[0,0],[0,0]],[[4147,0],[0,0]],[[0,0],[0,0]],[[8268,0],[0,0]],[[0,0],[0,0]],[[9828,13],[13,0]],[[0,0],[0,0]],[[6682,104],[104,0]],[[0,0],[0,0]],[[2171,286],[286,0]],[[0,0],[0,0]],[[39,312],[312,0]],[[0,0],[0,0]],[[-117,117],[117,0]],[[0],[0,0]],[[0],[0,13]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
