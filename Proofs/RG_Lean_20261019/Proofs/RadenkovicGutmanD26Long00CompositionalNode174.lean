/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode119
import Proofs.RadenkovicGutmanD26Long00CompositionalNode037
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e174 : NestedArithmetic.Expr 3 := .times e119 e037
noncomputable def p174 : NestedHorner.Poly 3 := [[[-48]]]
theorem step174 : p174=NestedArithmetic.mul p119 p037 := by decide +kernel
#print axioms step174
theorem h174 : NestedArithmetic.compile e174=p174 := StagedExprCompile.compile_times e174 e119 e037 p119 p037 p174 rfl h119 h037 step174
#print axioms h174
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
