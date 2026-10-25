/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode065
import Proofs.RadenkovicGutmanD35Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[35],[0]],[[0,0],[0]],[[560,0],[0]],[[0,0],[0]],[[3745,0],[0]],[[0,0],[0]],[[13580,0],[0]],[[0,0],[0]],[[28980,0],[0]],[[0,0],[0]],[[36960,35],[35]],[[0,0],[0]],[[27265,245],[245]],[[0,0],[0]],[[10500,560],[560]],[[0,0],[0]],[[1575,455],[455]],[[0,0],[0]],[[0,105],[105]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
