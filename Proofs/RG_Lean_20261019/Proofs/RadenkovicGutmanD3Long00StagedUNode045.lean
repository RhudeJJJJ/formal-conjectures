/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .rational 6
noncomputable def p045 : NestedHorner.Poly 3 := [[[6]]]
theorem h045 : NestedArithmetic.compile e045=p045 := by decide +kernel
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
