/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode134
import Proofs.RadenkovicGutmanD31Long00CompositionalNode135
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e136 : NestedArithmetic.Expr 3 := .plus e134 e135
noncomputable def p136 : NestedHorner.Poly 3 := [[[1]],[[0]],[[4]],[[0]],[[3]]]
theorem step136 : p136=NestedHorner.add p134 p135 := by decide +kernel
#print axioms step136
theorem h136 : NestedArithmetic.compile e136=p136 := StagedExprCompile.compile_plus e136 e134 e135 p134 p135 p136 rfl h134 h135 step136
#print axioms h136
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
