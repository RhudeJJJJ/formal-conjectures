/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode202
import Proofs.RadenkovicGutmanD28Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[62,0],[0,0]],[[0,0],[0,0]],[[720,0],[0,0]],[[0,0],[0,0]],[[4378,0],[0,0]],[[0,0],[0,0]],[[15740,0],[0,0]],[[0,0],[0,0]],[[35096,2],[2,0]],[[0,0],[0,0]],[[48892,44],[44,0]],[[0,0],[0,0]],[[41434,268],[268,0]],[[0,0],[0,0]],[[19834,664],[664,0]],[[0,0],[0,0]],[[4470,690],[690,0]],[[0,0],[0,0]],[[252,252],[252,2]],[[0],[0,0]],[[0],[0,28]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
