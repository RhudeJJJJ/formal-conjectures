/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode030
import Proofs.RadenkovicGutmanD38Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[38],[0]],[[0,0],[0]],[[608,0],[0]],[[0,0],[0]],[[4066,0],[0]],[[0,0],[0]],[[14744,0],[0]],[[0,0],[0]],[[31464,0],[0]],[[0,0],[0]],[[40128,38],[38]],[[0,0],[0]],[[29602,266],[266]],[[0,0],[0]],[[11400,608],[608]],[[0,0],[0]],[[1710,494],[494]],[[0,0],[0]],[[0,114],[114]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
