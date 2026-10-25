/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode044
import Proofs.RadenkovicGutmanD24Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,24]],[[0,0],[0,0]],[[216,216],[216,2]],[[0,0],[0]],[[3834,594],[594]],[[0,0],[0]],[[17046,576],[576]],[[0,0],[0]],[[35714,236],[236]],[[0,0],[0]],[[42316,40],[40]],[[0,0],[0]],[[30552,2],[2]],[[0]],[[13816]],[[0]],[[3890]],[[0]],[[652]],[[0]],[[58]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
