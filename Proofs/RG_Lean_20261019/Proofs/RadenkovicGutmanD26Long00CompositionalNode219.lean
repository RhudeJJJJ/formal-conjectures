/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode065
import Proofs.RadenkovicGutmanD26Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[26],[0]],[[0,0],[0]],[[416,0],[0]],[[0,0],[0]],[[2782,0],[0]],[[0,0],[0]],[[10088,0],[0]],[[0,0],[0]],[[21528,0],[0]],[[0,0],[0]],[[27456,26],[26]],[[0,0],[0]],[[20254,182],[182]],[[0,0],[0]],[[7800,416],[416]],[[0,0],[0]],[[1170,338],[338]],[[0,0],[0]],[[0,78],[78]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
