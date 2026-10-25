/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode065
import Proofs.RadenkovicGutmanD28Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[28],[0]],[[0,0],[0]],[[448,0],[0]],[[0,0],[0]],[[2996,0],[0]],[[0,0],[0]],[[10864,0],[0]],[[0,0],[0]],[[23184,0],[0]],[[0,0],[0]],[[29568,28],[28]],[[0,0],[0]],[[21812,196],[196]],[[0,0],[0]],[[8400,448],[448]],[[0,0],[0]],[[1260,364],[364]],[[0,0],[0]],[[0,84],[84]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
