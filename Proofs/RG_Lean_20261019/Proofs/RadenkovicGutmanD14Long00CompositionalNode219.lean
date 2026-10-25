/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode065
import Proofs.RadenkovicGutmanD14Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[14],[0]],[[0,0],[0]],[[224,0],[0]],[[0,0],[0]],[[1498,0],[0]],[[0,0],[0]],[[5432,0],[0]],[[0,0],[0]],[[11592,0],[0]],[[0,0],[0]],[[14784,14],[14]],[[0,0],[0]],[[10906,98],[98]],[[0,0],[0]],[[4200,224],[224]],[[0,0],[0]],[[630,182],[182]],[[0,0],[0]],[[0,42],[42]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
