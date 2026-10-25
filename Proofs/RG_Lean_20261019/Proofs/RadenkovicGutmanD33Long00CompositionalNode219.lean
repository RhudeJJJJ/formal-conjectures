/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode065
import Proofs.RadenkovicGutmanD33Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[33],[0]],[[0,0],[0]],[[528,0],[0]],[[0,0],[0]],[[3531,0],[0]],[[0,0],[0]],[[12804,0],[0]],[[0,0],[0]],[[27324,0],[0]],[[0,0],[0]],[[34848,33],[33]],[[0,0],[0]],[[25707,231],[231]],[[0,0],[0]],[[9900,528],[528]],[[0,0],[0]],[[1485,429],[429]],[[0,0],[0]],[[0,99],[99]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
