/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode065
import Proofs.RadenkovicGutmanD15Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[15],[0]],[[0,0],[0]],[[240,0],[0]],[[0,0],[0]],[[1605,0],[0]],[[0,0],[0]],[[5820,0],[0]],[[0,0],[0]],[[12420,0],[0]],[[0,0],[0]],[[15840,15],[15]],[[0,0],[0]],[[11685,105],[105]],[[0,0],[0]],[[4500,240],[240]],[[0,0],[0]],[[675,195],[195]],[[0,0],[0]],[[0,45],[45]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
