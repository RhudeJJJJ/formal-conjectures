/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode030
import Proofs.RadenkovicGutmanD30Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[30],[0]],[[0,0],[0]],[[450,0],[0,0]],[[0,0],[0,0]],[[2820,0],[0,0]],[[0,0],[0,0]],[[9570,0],[0,0]],[[0,0],[0,0]],[[19080,0],[0,0]],[[0,0],[0,0]],[[22680,30],[30,0]],[[0,0],[0,0]],[[15420,240],[240,0]],[[0,0],[0,0]],[[5010,660],[660,0]],[[0,0],[0,0]],[[90,720],[720,0]],[[0,0],[0,0]],[[-270,270],[270,0]],[[0],[0,0]],[[0],[0,30]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
