/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode065
import Proofs.RadenkovicGutmanD39Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[39],[0]],[[0,0],[0]],[[624,0],[0]],[[0,0],[0]],[[4173,0],[0]],[[0,0],[0]],[[15132,0],[0]],[[0,0],[0]],[[32292,0],[0]],[[0,0],[0]],[[41184,39],[39]],[[0,0],[0]],[[30381,273],[273]],[[0,0],[0]],[[11700,624],[624]],[[0,0],[0]],[[1755,507],[507]],[[0,0],[0]],[[0,117],[117]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
