/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e017 : NestedArithmetic.Expr 3 := .rational 2
noncomputable def p017 : NestedHorner.Poly 3 := [[[2]]]
theorem h017 : NestedArithmetic.compile e017=p017 := by decide +kernel
#print axioms h017
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
