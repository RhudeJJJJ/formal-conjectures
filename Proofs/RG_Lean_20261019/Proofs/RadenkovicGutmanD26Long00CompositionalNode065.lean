/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e065 : NestedArithmetic.Expr 3 := .rational (-1)
noncomputable def p065 : NestedHorner.Poly 3 := [[[-1]]]
theorem h065 : NestedArithmetic.compile e065=p065 := by decide +kernel
#print axioms h065
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
