/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode133
import Proofs.RadenkovicGutmanD4Long00CompositionalNode134
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e135 : NestedArithmetic.Expr 3 := .plus e133 e134
noncomputable def p135 : NestedHorner.Poly 3 := [[[1]],[[0]],[[4]],[[0]],[[3]]]
theorem step135 : p135=NestedHorner.add p133 p134 := by decide +kernel
#print axioms step135
theorem h135 : NestedArithmetic.compile e135=p135 := StagedExprCompile.compile_plus e135 e133 e134 p133 p134 p135 rfl h133 h134 step135
#print axioms h135
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
