/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode017
import Proofs.RadenkovicGutmanD4Long00CompositionalNode119
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e138 : NestedArithmetic.Expr 3 := .times e017 e119
noncomputable def p138 : NestedHorner.Poly 3 := [[[2]]]
theorem step138 : p138=NestedArithmetic.mul p017 p119 := by decide +kernel
#print axioms step138
theorem h138 : NestedArithmetic.compile e138=p138 := StagedExprCompile.compile_times e138 e017 e119 p017 p119 p138 rfl h017 h119 step138
#print axioms h138
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
