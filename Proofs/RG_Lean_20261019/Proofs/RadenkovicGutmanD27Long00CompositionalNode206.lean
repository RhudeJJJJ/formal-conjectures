/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode203
import Proofs.RadenkovicGutmanD27Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[115,0],[0,0]],[[0,0],[0,0]],[[1567,0],[0,0]],[[0,0],[0,0]],[[10034,0],[0,0]],[[0,0],[0,0]],[[36211,0],[0,0]],[[0,0],[0,0]],[[78672,2],[2,0]],[[0,0],[0,0]],[[104272,97],[97,0]],[[0,0],[0,0]],[[82070,638],[638,0]],[[0,0],[0,0]],[[35337,1506],[1506,0]],[[0,0],[0,0]],[[6741,1368],[1368,0]],[[0,0],[0,0]],[[243,405],[405,2]],[[0],[0,0]],[[0],[0,27]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
