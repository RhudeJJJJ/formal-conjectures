/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode065
import Proofs.RadenkovicGutmanD38Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[38],[0]],[[0,0],[0]],[[608,0],[0]],[[0,0],[0]],[[4066,0],[0]],[[0,0],[0]],[[14744,0],[0]],[[0,0],[0]],[[31464,0],[0]],[[0,0],[0]],[[40128,38],[38]],[[0,0],[0]],[[29602,266],[266]],[[0,0],[0]],[[11400,608],[608]],[[0,0],[0]],[[1710,494],[494]],[[0,0],[0]],[[0,114],[114]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
