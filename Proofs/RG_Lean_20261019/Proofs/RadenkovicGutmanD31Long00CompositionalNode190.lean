/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode030
import Proofs.RadenkovicGutmanD31Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e190 : NestedArithmetic.Expr 3 := .times e030 e003
noncomputable def p190 : NestedHorner.Poly 3 := [[[]],[[0]],[[31]]]
theorem step190 : p190=NestedArithmetic.mul p030 p003 := by decide +kernel
#print axioms step190
theorem h190 : NestedArithmetic.compile e190=p190 := StagedExprCompile.compile_times e190 e030 e003 p030 p003 p190 rfl h030 h003 step190
#print axioms h190
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
