/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode065
import Proofs.RadenkovicGutmanD43Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[43],[0]],[[0,0],[0]],[[688,0],[0]],[[0,0],[0]],[[4601,0],[0]],[[0,0],[0]],[[16684,0],[0]],[[0,0],[0]],[[35604,0],[0]],[[0,0],[0]],[[45408,43],[43]],[[0,0],[0]],[[33497,301],[301]],[[0,0],[0]],[[12900,688],[688]],[[0,0],[0]],[[1935,559],[559]],[[0,0],[0]],[[0,129],[129]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
