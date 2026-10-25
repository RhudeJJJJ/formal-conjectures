/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode191
import Proofs.RadenkovicGutmanD9Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[43,0],[0,0]],[[0,0],[0,0]],[[397,0],[0,0]],[[0,0],[0,0]],[[2060,0],[0,0]],[[0,0],[0,0]],[[6601,0],[0,0]],[[0,0],[0,0]],[[13512,2],[2,0]],[[0,0],[0,0]],[[17656,25],[25,0]],[[0,0],[0,0]],[[14264,116],[116,0]],[[0,0],[0,0]],[[6591,246],[246,0]],[[0,0],[0,0]],[[1449,234],[234,0]],[[0,0],[0,0]],[[81,81],[81,2]],[[0],[0,0]],[[0],[0,9]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
