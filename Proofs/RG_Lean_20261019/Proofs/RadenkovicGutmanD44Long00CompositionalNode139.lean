/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode017
import Proofs.RadenkovicGutmanD44Long00CompositionalNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e139 : NestedArithmetic.Expr 3 := .times e017 e120
noncomputable def p139 : NestedHorner.Poly 3 := [[[2]]]
theorem step139 : p139=NestedArithmetic.mul p017 p120 := by decide +kernel
#print axioms step139
theorem h139 : NestedArithmetic.compile e139=p139 := StagedExprCompile.compile_times e139 e017 e120 p017 p120 p139 rfl h017 h120 step139
#print axioms h139
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
