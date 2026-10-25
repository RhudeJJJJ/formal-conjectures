/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode030
import Proofs.RadenkovicGutmanD41Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .times e030 e032
noncomputable def p033 : NestedHorner.Poly 3 := [[[0],[0,41]],[[0,0],[0]],[[-369,369],[369]],[[0,0],[0]],[[123,984],[984]],[[0,0],[0]],[[6847,902],[902]],[[0,0],[0]],[[21074,328],[328]],[[0,0],[0]],[[30996,41],[41]],[[0]],[[26076]],[[0]],[[13079]],[[0]],[[3854]],[[0]],[[615]],[[0]],[[41]]]
theorem step033 : p033=NestedArithmetic.mul p030 p032 := by decide +kernel
#print axioms step033
theorem h033 : NestedArithmetic.compile e033=p033 := StagedExprCompile.compile_times e033 e030 e032 p030 p032 p033 rfl h030 h032 step033
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
