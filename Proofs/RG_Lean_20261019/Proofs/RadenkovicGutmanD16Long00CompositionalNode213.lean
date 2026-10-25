/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode030
import Proofs.RadenkovicGutmanD16Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[16],[0]],[[0,0],[0]],[[240,0],[0,0]],[[0,0],[0,0]],[[1504,0],[0,0]],[[0,0],[0,0]],[[5104,0],[0,0]],[[0,0],[0,0]],[[10176,0],[0,0]],[[0,0],[0,0]],[[12096,16],[16,0]],[[0,0],[0,0]],[[8224,128],[128,0]],[[0,0],[0,0]],[[2672,352],[352,0]],[[0,0],[0,0]],[[48,384],[384,0]],[[0,0],[0,0]],[[-144,144],[144,0]],[[0],[0,0]],[[0],[0,16]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
