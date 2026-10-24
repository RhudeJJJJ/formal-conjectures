/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode018
import Proofs.RadenkovicGutmanD2Long00CompositionalNode017
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e018 e017
noncomputable def p043 : NestedHorner.Poly 3 := [[[2]],[[0]],[[2]]]
theorem step043 : p043=NestedHorner.add p018 p017 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e018 e017 p018 p017 p043 rfl h018 h017 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
