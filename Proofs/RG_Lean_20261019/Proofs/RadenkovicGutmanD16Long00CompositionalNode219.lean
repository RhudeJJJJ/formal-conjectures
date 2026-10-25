/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode065
import Proofs.RadenkovicGutmanD16Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[16],[0]],[[0,0],[0]],[[256,0],[0]],[[0,0],[0]],[[1712,0],[0]],[[0,0],[0]],[[6208,0],[0]],[[0,0],[0]],[[13248,0],[0]],[[0,0],[0]],[[16896,16],[16]],[[0,0],[0]],[[12464,112],[112]],[[0,0],[0]],[[4800,256],[256]],[[0,0],[0]],[[720,208],[208]],[[0,0],[0]],[[0,48],[48]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
