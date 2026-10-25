/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e000 : NestedArithmetic.Expr 3 := .indet 0
noncomputable def p000 : NestedHorner.Poly 3 := [[],[[1]]]
theorem h000 : NestedArithmetic.compile e000=p000 := by decide +kernel
#print axioms h000
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
