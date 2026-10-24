/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode132
import Proofs.RadenkovicGutmanD2Long00CompositionalNode133
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e134 : NestedArithmetic.Expr 3 := .plus e132 e133
noncomputable def p134 : NestedHorner.Poly 3 := [[[1]],[[0]],[[4]],[[0]],[[3]]]
theorem step134 : p134=NestedHorner.add p132 p133 := by decide +kernel
#print axioms step134
theorem h134 : NestedArithmetic.compile e134=p134 := StagedExprCompile.compile_plus e134 e132 e133 p132 p133 p134 rfl h132 h133 step134
#print axioms h134
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
