/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .rational (-1)
noncomputable def p064 : NestedHorner.Poly 3 := [[[-1]]]
theorem h064 : NestedArithmetic.compile e064=p064 := by decide +kernel
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
