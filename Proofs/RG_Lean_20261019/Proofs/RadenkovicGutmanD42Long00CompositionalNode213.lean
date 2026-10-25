/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode030
import Proofs.RadenkovicGutmanD42Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[42],[0]],[[0,0],[0]],[[630,0],[0,0]],[[0,0],[0,0]],[[3948,0],[0,0]],[[0,0],[0,0]],[[13398,0],[0,0]],[[0,0],[0,0]],[[26712,0],[0,0]],[[0,0],[0,0]],[[31752,42],[42,0]],[[0,0],[0,0]],[[21588,336],[336,0]],[[0,0],[0,0]],[[7014,924],[924,0]],[[0,0],[0,0]],[[126,1008],[1008,0]],[[0,0],[0,0]],[[-378,378],[378,0]],[[0],[0,0]],[[0],[0,42]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
