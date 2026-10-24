/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode043
import Proofs.RadenkovicGutmanD2Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e060 : NestedArithmetic.Expr 3 := .times e043 e050
noncomputable def p060 : NestedHorner.Poly 3 := [[[0],[0,2]],[[0,0],[0,0]],[[18,18],[18,2]],[[0,0],[0]],[[336,66],[66]],[[0,0],[0]],[[1712,92],[92]],[[0,0],[0]],[[4254,60],[60]],[[0,0],[0]],[[6148,18],[18]],[[0,0],[0]],[[5560,2],[2]],[[0]],[[3234]],[[0]],[[1206]],[[0]],[[278]],[[0]],[[36]],[[0]],[[2]]]
theorem step060 : p060=NestedArithmetic.mul p043 p050 := by decide +kernel
#print axioms step060
theorem h060 : NestedArithmetic.compile e060=p060 := StagedExprCompile.compile_times e060 e043 e050 p043 p050 p060 rfl h043 h050 step060
#print axioms h060
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
