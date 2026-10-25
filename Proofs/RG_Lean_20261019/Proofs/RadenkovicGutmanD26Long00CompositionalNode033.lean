/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode030
import Proofs.RadenkovicGutmanD26Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .times e030 e032
noncomputable def p033 : NestedHorner.Poly 3 := [[[0],[0,26]],[[0,0],[0]],[[-234,234],[234]],[[0,0],[0]],[[78,624],[624]],[[0,0],[0]],[[4342,572],[572]],[[0,0],[0]],[[13364,208],[208]],[[0,0],[0]],[[19656,26],[26]],[[0]],[[16536]],[[0]],[[8294]],[[0]],[[2444]],[[0]],[[390]],[[0]],[[26]]]
theorem step033 : p033=NestedArithmetic.mul p030 p032 := by decide +kernel
#print axioms step033
theorem h033 : NestedArithmetic.compile e033=p033 := StagedExprCompile.compile_times e033 e030 e032 p030 p032 p033 rfl h030 h032 step033
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
