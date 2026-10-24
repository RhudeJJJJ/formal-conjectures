/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode129
import Proofs.RadenkovicGutmanD2Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e130 : NestedArithmetic.Expr 3 := .times e129 e003
noncomputable def p130 : NestedHorner.Poly 3 := [[[]],[[0]],[[4]]]
theorem step130 : p130=NestedArithmetic.mul p129 p003 := by decide +kernel
#print axioms step130
theorem h130 : NestedArithmetic.compile e130=p130 := StagedExprCompile.compile_times e130 e129 e003 p129 p003 p130 rfl h129 h003 step130
#print axioms h130
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
