/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode011
import Proofs.RadenkovicGutmanD32Long00CompositionalNode002
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e012 : NestedArithmetic.Expr 3 := .plus e011 e002
noncomputable def p012 : NestedHorner.Poly 3 := [[[3]],[[0]],[[4]],[[0]],[[1]]]
theorem step012 : p012=NestedHorner.add p011 p002 := by decide +kernel
#print axioms step012
theorem h012 : NestedArithmetic.compile e012=p012 := StagedExprCompile.compile_plus e012 e011 e002 p011 p002 p012 rfl h011 h002 step012
#print axioms h012
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
