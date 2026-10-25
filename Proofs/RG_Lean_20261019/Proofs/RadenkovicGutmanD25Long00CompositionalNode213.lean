/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode030
import Proofs.RadenkovicGutmanD25Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[25],[0]],[[0,0],[0]],[[375,0],[0,0]],[[0,0],[0,0]],[[2350,0],[0,0]],[[0,0],[0,0]],[[7975,0],[0,0]],[[0,0],[0,0]],[[15900,0],[0,0]],[[0,0],[0,0]],[[18900,25],[25,0]],[[0,0],[0,0]],[[12850,200],[200,0]],[[0,0],[0,0]],[[4175,550],[550,0]],[[0,0],[0,0]],[[75,600],[600,0]],[[0,0],[0,0]],[[-225,225],[225,0]],[[0],[0,0]],[[0],[0,25]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
