/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e063 : NestedArithmetic.Expr 3 := .rational (-1)
noncomputable def p063 : NestedHorner.Poly 3 := [[[-1]]]
theorem h063 : NestedArithmetic.compile e063=p063 := by decide +kernel
#print axioms h063
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
