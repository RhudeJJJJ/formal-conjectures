/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode030
import Proofs.RadenkovicGutmanD23Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[23],[0]],[[0,0],[0]],[[345,0],[0,0]],[[0,0],[0,0]],[[2162,0],[0,0]],[[0,0],[0,0]],[[7337,0],[0,0]],[[0,0],[0,0]],[[14628,0],[0,0]],[[0,0],[0,0]],[[17388,23],[23,0]],[[0,0],[0,0]],[[11822,184],[184,0]],[[0,0],[0,0]],[[3841,506],[506,0]],[[0,0],[0,0]],[[69,552],[552,0]],[[0,0],[0,0]],[[-207,207],[207,0]],[[0],[0,0]],[[0],[0,23]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
