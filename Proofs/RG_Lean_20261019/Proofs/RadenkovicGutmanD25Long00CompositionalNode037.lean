/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e037 : NestedArithmetic.Expr 3 := .rational (-23)
noncomputable def p037 : NestedHorner.Poly 3 := [[[-23]]]
theorem h037 : NestedArithmetic.compile e037=p037 := by decide +kernel
#print axioms h037
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
