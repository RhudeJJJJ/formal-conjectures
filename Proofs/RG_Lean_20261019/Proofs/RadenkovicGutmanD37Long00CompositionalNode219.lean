/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode065
import Proofs.RadenkovicGutmanD37Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[37],[0]],[[0,0],[0]],[[592,0],[0]],[[0,0],[0]],[[3959,0],[0]],[[0,0],[0]],[[14356,0],[0]],[[0,0],[0]],[[30636,0],[0]],[[0,0],[0]],[[39072,37],[37]],[[0,0],[0]],[[28823,259],[259]],[[0,0],[0]],[[11100,592],[592]],[[0,0],[0]],[[1665,481],[481]],[[0,0],[0]],[[0,111],[111]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
