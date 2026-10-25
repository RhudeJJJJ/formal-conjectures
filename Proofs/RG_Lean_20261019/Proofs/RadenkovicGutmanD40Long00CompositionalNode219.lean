/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode065
import Proofs.RadenkovicGutmanD40Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[40],[0]],[[0,0],[0]],[[640,0],[0]],[[0,0],[0]],[[4280,0],[0]],[[0,0],[0]],[[15520,0],[0]],[[0,0],[0]],[[33120,0],[0]],[[0,0],[0]],[[42240,40],[40]],[[0,0],[0]],[[31160,280],[280]],[[0,0],[0]],[[12000,640],[640]],[[0,0],[0]],[[1800,520],[520]],[[0,0],[0]],[[0,120],[120]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
