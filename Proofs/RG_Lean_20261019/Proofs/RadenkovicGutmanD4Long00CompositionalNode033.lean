/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .rational (-4)
noncomputable def p033 : NestedHorner.Poly 3 := [[[-4]]]
theorem h033 : NestedArithmetic.compile e033=p033 := by decide +kernel
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
