/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode030
import Proofs.RadenkovicGutmanD26Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[26],[0]],[[0,0],[0]],[[390,0],[0,0]],[[0,0],[0,0]],[[2444,0],[0,0]],[[0,0],[0,0]],[[8294,0],[0,0]],[[0,0],[0,0]],[[16536,0],[0,0]],[[0,0],[0,0]],[[19656,26],[26,0]],[[0,0],[0,0]],[[13364,208],[208,0]],[[0,0],[0,0]],[[4342,572],[572,0]],[[0,0],[0,0]],[[78,624],[624,0]],[[0,0],[0,0]],[[-234,234],[234,0]],[[0],[0,0]],[[0],[0,26]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
