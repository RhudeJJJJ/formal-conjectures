/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode139
import Proofs.RadenkovicGutmanD40Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e189 : NestedArithmetic.Expr 3 := .times e139 e122
noncomputable def p189 : NestedHorner.Poly 3 := [[[2]]]
theorem step189 : p189=NestedArithmetic.mul p139 p122 := by decide +kernel
#print axioms step189
theorem h189 : NestedArithmetic.compile e189=p189 := StagedExprCompile.compile_times e189 e139 e122 p139 p122 p189 rfl h139 h122 step189
#print axioms h189
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
