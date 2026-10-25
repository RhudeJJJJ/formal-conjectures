/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode021
import Proofs.RadenkovicGutmanD10Long00CompositionalNode025
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e026 : NestedArithmetic.Expr 3 := .plus e021 e025
noncomputable def p026 : NestedHorner.Poly 3 := [[[0,1]],[[0]],[[9]],[[0]],[[24]],[[0]],[[22]],[[0]],[[8]],[[0]],[[1]]]
theorem step026 : p026=NestedHorner.add p021 p025 := by decide +kernel
#print axioms step026
theorem h026 : NestedArithmetic.compile e026=p026 := StagedExprCompile.compile_plus e026 e021 e025 p021 p025 p026 rfl h021 h025 step026
#print axioms h026
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
