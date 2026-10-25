/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e009 : NestedArithmetic.Expr 3 := .rational 4
noncomputable def p009 : NestedHorner.Poly 3 := [[[4]]]
theorem h009 : NestedArithmetic.compile e009=p009 := by decide +kernel
#print axioms h009
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
