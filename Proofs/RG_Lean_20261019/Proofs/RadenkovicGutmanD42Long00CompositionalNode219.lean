/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode065
import Proofs.RadenkovicGutmanD42Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[42],[0]],[[0,0],[0]],[[672,0],[0]],[[0,0],[0]],[[4494,0],[0]],[[0,0],[0]],[[16296,0],[0]],[[0,0],[0]],[[34776,0],[0]],[[0,0],[0]],[[44352,42],[42]],[[0,0],[0]],[[32718,294],[294]],[[0,0],[0]],[[12600,672],[672]],[[0,0],[0]],[[1890,546],[546]],[[0,0],[0]],[[0,126],[126]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
