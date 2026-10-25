/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode030
import Proofs.RadenkovicGutmanD14Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[14],[0]],[[0,0],[0]],[[210,0],[0,0]],[[0,0],[0,0]],[[1316,0],[0,0]],[[0,0],[0,0]],[[4466,0],[0,0]],[[0,0],[0,0]],[[8904,0],[0,0]],[[0,0],[0,0]],[[10584,14],[14,0]],[[0,0],[0,0]],[[7196,112],[112,0]],[[0,0],[0,0]],[[2338,308],[308,0]],[[0,0],[0,0]],[[42,336],[336,0]],[[0,0],[0,0]],[[-126,126],[126,0]],[[0],[0,0]],[[0],[0,14]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
