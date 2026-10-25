/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode030
import Proofs.RadenkovicGutmanD6Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[6],[0]],[[0,0],[0]],[[90,0],[0,0]],[[0,0],[0,0]],[[564,0],[0,0]],[[0,0],[0,0]],[[1914,0],[0,0]],[[0,0],[0,0]],[[3816,0],[0,0]],[[0,0],[0,0]],[[4536,6],[6,0]],[[0,0],[0,0]],[[3084,48],[48,0]],[[0,0],[0,0]],[[1002,132],[132,0]],[[0,0],[0,0]],[[18,144],[144,0]],[[0,0],[0,0]],[[-54,54],[54,0]],[[0],[0,0]],[[0],[0,6]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
