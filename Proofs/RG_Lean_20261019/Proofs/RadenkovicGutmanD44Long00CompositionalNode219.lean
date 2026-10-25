/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode065
import Proofs.RadenkovicGutmanD44Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[44],[0]],[[0,0],[0]],[[704,0],[0]],[[0,0],[0]],[[4708,0],[0]],[[0,0],[0]],[[17072,0],[0]],[[0,0],[0]],[[36432,0],[0]],[[0,0],[0]],[[46464,44],[44]],[[0,0],[0]],[[34276,308],[308]],[[0,0],[0]],[[13200,704],[704]],[[0,0],[0]],[[1980,572],[572]],[[0,0],[0]],[[0,132],[132]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
