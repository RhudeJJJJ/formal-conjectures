/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode065
import Proofs.RadenkovicGutmanD25Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[25],[0]],[[0,0],[0]],[[400,0],[0]],[[0,0],[0]],[[2675,0],[0]],[[0,0],[0]],[[9700,0],[0]],[[0,0],[0]],[[20700,0],[0]],[[0,0],[0]],[[26400,25],[25]],[[0,0],[0]],[[19475,175],[175]],[[0,0],[0]],[[7500,400],[400]],[[0,0],[0]],[[1125,325],[325]],[[0,0],[0]],[[0,75],[75]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
