/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e002 : NestedArithmetic.Expr 3 := .rational 3
noncomputable def p002 : NestedHorner.Poly 3 := [[[3]]]
theorem h002 : NestedArithmetic.compile e002=p002 := by decide +kernel
#print axioms h002
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
