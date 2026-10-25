/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e034 : NestedArithmetic.Expr 3 := .rational (-20)
noncomputable def p034 : NestedHorner.Poly 3 := [[[-20]]]
theorem h034 : NestedArithmetic.compile e034=p034 := by decide +kernel
#print axioms h034
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
