/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e006 : NestedArithmetic.Expr 3 := .rational 1
noncomputable def p006 : NestedHorner.Poly 3 := [[[1]]]
theorem h006 : NestedArithmetic.compile e006=p006 := by decide +kernel
#print axioms h006
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
