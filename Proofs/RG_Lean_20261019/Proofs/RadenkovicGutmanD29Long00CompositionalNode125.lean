/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode124
import Proofs.RadenkovicGutmanD29Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e125 : NestedArithmetic.Expr 3 := .times e124 e003
noncomputable def p125 : NestedHorner.Poly 3 := [[[]],[[0]],[[3]]]
theorem step125 : p125=NestedArithmetic.mul p124 p003 := by decide +kernel
#print axioms step125
theorem h125 : NestedArithmetic.compile e125=p125 := StagedExprCompile.compile_times e125 e124 e003 p124 p003 p125 rfl h124 h003 step125
#print axioms h125
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
