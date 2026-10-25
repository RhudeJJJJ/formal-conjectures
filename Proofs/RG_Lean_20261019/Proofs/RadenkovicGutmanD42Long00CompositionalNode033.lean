/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode030
import Proofs.RadenkovicGutmanD42Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .times e030 e032
noncomputable def p033 : NestedHorner.Poly 3 := [[[0],[0,42]],[[0,0],[0]],[[-378,378],[378]],[[0,0],[0]],[[126,1008],[1008]],[[0,0],[0]],[[7014,924],[924]],[[0,0],[0]],[[21588,336],[336]],[[0,0],[0]],[[31752,42],[42]],[[0]],[[26712]],[[0]],[[13398]],[[0]],[[3948]],[[0]],[[630]],[[0]],[[42]]]
theorem step033 : p033=NestedArithmetic.mul p030 p032 := by decide +kernel
#print axioms step033
theorem h033 : NestedArithmetic.compile e033=p033 := StagedExprCompile.compile_times e033 e030 e032 p030 p032 p033 rfl h030 h032 step033
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
