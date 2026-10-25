/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode184
import Proofs.RadenkovicGutmanD38Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[38,0],[0]],[[0,0],[0]],[[608,0],[0]],[[0,0],[0]],[[4066,0],[0]],[[0,0],[0]],[[14744,0],[0]],[[0,0],[0]],[[31464,0],[0]],[[0,0],[0]],[[40128,38],[38]],[[0,0],[0]],[[29602,266],[266]],[[0,0],[0]],[[11400,608],[608]],[[0,0],[0]],[[1710,494],[494]],[[0,0],[0]],[[0,114],[114]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
