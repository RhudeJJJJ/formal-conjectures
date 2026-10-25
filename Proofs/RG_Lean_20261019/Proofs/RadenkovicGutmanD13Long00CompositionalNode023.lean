/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode021
import Proofs.RadenkovicGutmanD13Long00CompositionalNode022
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e023 : NestedArithmetic.Expr 3 := .plus e021 e022
noncomputable def p023 : NestedHorner.Poly 3 := [[[],[1]],[[0]],[[9]],[[0]],[[24]],[[0]],[[22]],[[0]],[[8]],[[0]],[[1]]]
theorem step023 : p023=NestedHorner.add p021 p022 := by decide +kernel
#print axioms step023
theorem h023 : NestedArithmetic.compile e023=p023 := StagedExprCompile.compile_plus e023 e021 e022 p021 p022 p023 rfl h021 h022 step023
#print axioms h023
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
