/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode202
import Proofs.RadenkovicGutmanD24Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[58,0],[0,0]],[[0,0],[0,0]],[[652,0],[0,0]],[[0,0],[0,0]],[[3890,0],[0,0]],[[0,0],[0,0]],[[13816,0],[0,0]],[[0,0],[0,0]],[[30552,2],[2,0]],[[0,0],[0,0]],[[42316,40],[40,0]],[[0,0],[0,0]],[[35714,236],[236,0]],[[0,0],[0,0]],[[17046,576],[576,0]],[[0,0],[0,0]],[[3834,594],[594,0]],[[0,0],[0,0]],[[216,216],[216,2]],[[0],[0,0]],[[0],[0,24]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
