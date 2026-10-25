/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode046
import Proofs.RadenkovicGutmanD31Long00CompositionalNode006
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e194 : NestedArithmetic.Expr 3 := .times e046 e006
noncomputable def p194 : NestedHorner.Poly 3 := [[[62]]]
theorem step194 : p194=NestedArithmetic.mul p046 p006 := by decide +kernel
#print axioms step194
theorem h194 : NestedArithmetic.compile e194=p194 := StagedExprCompile.compile_times e194 e046 e006 p046 p006 p194 rfl h046 h006 step194
#print axioms h194
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
