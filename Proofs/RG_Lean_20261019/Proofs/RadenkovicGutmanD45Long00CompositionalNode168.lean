/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode150
import Proofs.RadenkovicGutmanD45Long00CompositionalNode154
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e168 : NestedArithmetic.Expr 3 := .times e150 e154
noncomputable def p168 : NestedHorner.Poly 3 := [[[1]],[[0,0]],[[15,0]],[[0,0]],[[94,0]],[[0,0]],[[319,0]],[[0,0]],[[636,0]],[[0,0]],[[757,1]],[[0,0]],[[522,7]],[[0,0]],[[189,16]],[[0,0]],[[27,13]],[[0,0]],[[0,3]]]
theorem step168 : p168=NestedArithmetic.mul p150 p154 := by decide +kernel
#print axioms step168
theorem h168 : NestedArithmetic.compile e168=p168 := StagedExprCompile.compile_times e168 e150 e154 p150 p154 p168 rfl h150 h154 step168
#print axioms h168
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
