/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode065
import Proofs.RadenkovicGutmanD10Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[10],[0]],[[0,0],[0]],[[160,0],[0]],[[0,0],[0]],[[1070,0],[0]],[[0,0],[0]],[[3880,0],[0]],[[0,0],[0]],[[8280,0],[0]],[[0,0],[0]],[[10560,10],[10]],[[0,0],[0]],[[7790,70],[70]],[[0,0],[0]],[[3000,160],[160]],[[0,0],[0]],[[450,130],[130]],[[0,0],[0]],[[0,30],[30]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
