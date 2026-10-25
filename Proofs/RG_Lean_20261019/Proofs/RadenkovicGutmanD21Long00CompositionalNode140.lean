/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode139
import Proofs.RadenkovicGutmanD21Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e140 : NestedArithmetic.Expr 3 := .times e139 e003
noncomputable def p140 : NestedHorner.Poly 3 := [[[]],[[0]],[[2]]]
theorem step140 : p140=NestedArithmetic.mul p139 p003 := by decide +kernel
#print axioms step140
theorem h140 : NestedArithmetic.compile e140=p140 := StagedExprCompile.compile_times e140 e139 e003 p139 p003 p140 rfl h139 h003 step140
#print axioms h140
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
