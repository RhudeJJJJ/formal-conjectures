/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode144
import Proofs.RadenkovicGutmanD30Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e145 : NestedArithmetic.Expr 3 := .times e144 e122
noncomputable def p145 : NestedHorner.Poly 3 := [[[1]],[[0]],[[8]],[[0]],[[22]],[[0]],[[24]],[[0]],[[9]]]
theorem step145 : p145=NestedArithmetic.mul p144 p122 := by decide +kernel
#print axioms step145
theorem h145 : NestedArithmetic.compile e145=p145 := StagedExprCompile.compile_times e145 e144 e122 p144 p122 p145 rfl h144 h122 step145
#print axioms h145
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
