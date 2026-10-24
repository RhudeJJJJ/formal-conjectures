/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode009
import Proofs.RadenkovicGutmanD4Long00CompositionalNode119
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e130 : NestedArithmetic.Expr 3 := .times e009 e119
noncomputable def p130 : NestedHorner.Poly 3 := [[[4]]]
theorem step130 : p130=NestedArithmetic.mul p009 p119 := by decide +kernel
#print axioms step130
theorem h130 : NestedArithmetic.compile e130=p130 := StagedExprCompile.compile_times e130 e009 e119 p009 p119 p130 rfl h009 h119 step130
#print axioms h130
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
