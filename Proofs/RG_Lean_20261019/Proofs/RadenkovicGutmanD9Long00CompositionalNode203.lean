/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode202
import Proofs.RadenkovicGutmanD9Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[43,0],[0,0]],[[0,0],[0,0]],[[397,0],[0,0]],[[0,0],[0,0]],[[2060,0],[0,0]],[[0,0],[0,0]],[[6601,0],[0,0]],[[0,0],[0,0]],[[13512,2],[2,0]],[[0,0],[0,0]],[[17656,25],[25,0]],[[0,0],[0,0]],[[14264,116],[116,0]],[[0,0],[0,0]],[[6591,246],[246,0]],[[0,0],[0,0]],[[1449,234],[234,0]],[[0,0],[0,0]],[[81,81],[81,2]],[[0],[0,0]],[[0],[0,9]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
