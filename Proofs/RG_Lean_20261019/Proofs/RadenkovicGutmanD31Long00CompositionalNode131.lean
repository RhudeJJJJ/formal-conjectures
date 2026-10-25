/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode009
import Proofs.RadenkovicGutmanD31Long00CompositionalNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e131 : NestedArithmetic.Expr 3 := .times e009 e120
noncomputable def p131 : NestedHorner.Poly 3 := [[[4]]]
theorem step131 : p131=NestedArithmetic.mul p009 p120 := by decide +kernel
#print axioms step131
theorem h131 : NestedArithmetic.compile e131=p131 := StagedExprCompile.compile_times e131 e009 e120 p009 p120 p131 rfl h009 h120 step131
#print axioms h131
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
