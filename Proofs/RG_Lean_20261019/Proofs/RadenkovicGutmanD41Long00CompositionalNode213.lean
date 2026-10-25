/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode030
import Proofs.RadenkovicGutmanD41Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[41],[0]],[[0,0],[0]],[[615,0],[0,0]],[[0,0],[0,0]],[[3854,0],[0,0]],[[0,0],[0,0]],[[13079,0],[0,0]],[[0,0],[0,0]],[[26076,0],[0,0]],[[0,0],[0,0]],[[30996,41],[41,0]],[[0,0],[0,0]],[[21074,328],[328,0]],[[0,0],[0,0]],[[6847,902],[902,0]],[[0,0],[0,0]],[[123,984],[984,0]],[[0,0],[0,0]],[[-369,369],[369,0]],[[0],[0,0]],[[0],[0,41]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
