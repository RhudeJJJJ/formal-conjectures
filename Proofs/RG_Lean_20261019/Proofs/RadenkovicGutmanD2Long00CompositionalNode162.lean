/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode117
import Proofs.RadenkovicGutmanD2Long00CompositionalNode161
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e162 : NestedArithmetic.Expr 3 := .times e117 e161
noncomputable def p162 : NestedHorner.Poly 3 := [[[0],[0]],[[0,0],[0]],[[8,0],[0,0]],[[0,0],[0,0]],[[112,0],[0,0]],[[0,0],[0,0]],[[648,0],[0,0]],[[0,0],[0,0]],[[2000,0],[0,0]],[[0,0],[0,0]],[[3552,0],[0,0]],[[0,0],[0,0]],[[3664,0],[0,0]],[[0,0],[0,0]],[[2120,0],[0,0]],[[0,0],[0,0]],[[624,0],[0,0]],[[0,0],[0,0]],[[72,0],[0,0]],[[0],[0,0]],[[0],[0,0]]]
theorem step162 : p162=NestedArithmetic.mul p117 p161 := by decide +kernel
#print axioms step162
theorem h162 : NestedArithmetic.compile e162=p162 := StagedExprCompile.compile_times e162 e117 e161 p117 p161 p162 rfl h117 h161 step162
#print axioms h162
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
