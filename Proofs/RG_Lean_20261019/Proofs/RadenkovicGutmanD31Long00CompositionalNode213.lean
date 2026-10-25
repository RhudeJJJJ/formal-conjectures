/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode030
import Proofs.RadenkovicGutmanD31Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[31],[0]],[[0,0],[0]],[[465,0],[0,0]],[[0,0],[0,0]],[[2914,0],[0,0]],[[0,0],[0,0]],[[9889,0],[0,0]],[[0,0],[0,0]],[[19716,0],[0,0]],[[0,0],[0,0]],[[23436,31],[31,0]],[[0,0],[0,0]],[[15934,248],[248,0]],[[0,0],[0,0]],[[5177,682],[682,0]],[[0,0],[0,0]],[[93,744],[744,0]],[[0,0],[0,0]],[[-279,279],[279,0]],[[0],[0,0]],[[0],[0,31]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
