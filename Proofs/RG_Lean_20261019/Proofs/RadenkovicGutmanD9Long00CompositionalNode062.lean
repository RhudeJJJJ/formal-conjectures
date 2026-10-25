/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode044
import Proofs.RadenkovicGutmanD9Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,9]],[[0,0],[0,0]],[[81,81],[81,2]],[[0,0],[0]],[[1449,234],[234]],[[0,0],[0]],[[6591,246],[246]],[[0,0],[0]],[[14264,116],[116]],[[0,0],[0]],[[17656,25],[25]],[[0,0],[0]],[[13512,2],[2]],[[0]],[[6601]],[[0]],[[2060]],[[0]],[[397]],[[0]],[[43]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
