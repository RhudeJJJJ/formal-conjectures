/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e046 : NestedArithmetic.Expr 3 := .rational 80
noncomputable def p046 : NestedHorner.Poly 3 := [[[80]]]
theorem h046 : NestedArithmetic.compile e046=p046 := by decide +kernel
#print axioms h046
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
