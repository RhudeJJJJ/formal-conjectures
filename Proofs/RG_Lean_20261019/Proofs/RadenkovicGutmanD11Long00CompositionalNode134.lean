/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode133
import Proofs.RadenkovicGutmanD11Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e134 : NestedArithmetic.Expr 3 := .times e133 e122
noncomputable def p134 : NestedHorner.Poly 3 := [[[1]],[[0]],[[4]]]
theorem step134 : p134=NestedArithmetic.mul p133 p122 := by decide +kernel
#print axioms step134
theorem h134 : NestedArithmetic.compile e134=p134 := StagedExprCompile.compile_times e134 e133 e122 p133 p122 p134 rfl h133 h122 step134
#print axioms h134
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
