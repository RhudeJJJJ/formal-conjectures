/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode030
import Proofs.RadenkovicGutmanD21Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[21],[0]],[[0,0],[0]],[[315,0],[0,0]],[[0,0],[0,0]],[[1974,0],[0,0]],[[0,0],[0,0]],[[6699,0],[0,0]],[[0,0],[0,0]],[[13356,0],[0,0]],[[0,0],[0,0]],[[15876,21],[21,0]],[[0,0],[0,0]],[[10794,168],[168,0]],[[0,0],[0,0]],[[3507,462],[462,0]],[[0,0],[0,0]],[[63,504],[504,0]],[[0,0],[0,0]],[[-189,189],[189,0]],[[0],[0,0]],[[0],[0,21]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
