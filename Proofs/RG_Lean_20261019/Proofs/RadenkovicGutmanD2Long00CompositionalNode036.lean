/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e036 : NestedArithmetic.Expr 3 := .rational 0
noncomputable def p036 : NestedHorner.Poly 3 := [[[0]]]
theorem h036 : NestedArithmetic.compile e036=p036 := by decide +kernel
#print axioms h036
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
