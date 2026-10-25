/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode191
import Proofs.RadenkovicGutmanD24Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[58,0],[0,0]],[[0,0],[0,0]],[[652,0],[0,0]],[[0,0],[0,0]],[[3890,0],[0,0]],[[0,0],[0,0]],[[13816,0],[0,0]],[[0,0],[0,0]],[[30552,2],[2,0]],[[0,0],[0,0]],[[42316,40],[40,0]],[[0,0],[0,0]],[[35714,236],[236,0]],[[0,0],[0,0]],[[17046,576],[576,0]],[[0,0],[0,0]],[[3834,594],[594,0]],[[0,0],[0,0]],[[216,216],[216,2]],[[0],[0,0]],[[0],[0,24]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
