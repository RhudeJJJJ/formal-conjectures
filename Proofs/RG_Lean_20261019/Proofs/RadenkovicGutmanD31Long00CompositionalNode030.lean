/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e030 : NestedArithmetic.Expr 3 := .rational 31
noncomputable def p030 : NestedHorner.Poly 3 := [[[31]]]
theorem h030 : NestedArithmetic.compile e030=p030 := by decide +kernel
#print axioms h030
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
