/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode030
import Proofs.RadenkovicGutmanD39Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[39],[0]],[[0,0],[0]],[[585,0],[0,0]],[[0,0],[0,0]],[[3666,0],[0,0]],[[0,0],[0,0]],[[12441,0],[0,0]],[[0,0],[0,0]],[[24804,0],[0,0]],[[0,0],[0,0]],[[29484,39],[39,0]],[[0,0],[0,0]],[[20046,312],[312,0]],[[0,0],[0,0]],[[6513,858],[858,0]],[[0,0],[0,0]],[[117,936],[936,0]],[[0,0],[0,0]],[[-351,351],[351,0]],[[0],[0,0]],[[0],[0,39]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
