/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode137
import Proofs.RadenkovicGutmanD11Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e138 : NestedArithmetic.Expr 3 := .times e137 e122
noncomputable def p138 : NestedHorner.Poly 3 := [[[1]],[[0]],[[7]],[[0]],[[16]],[[0]],[[13]],[[0]],[[3]]]
theorem step138 : p138=NestedArithmetic.mul p137 p122 := by decide +kernel
#print axioms step138
theorem h138 : NestedArithmetic.compile e138=p138 := StagedExprCompile.compile_times e138 e137 e122 p137 p122 p138 rfl h137 h122 step138
#print axioms h138
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
