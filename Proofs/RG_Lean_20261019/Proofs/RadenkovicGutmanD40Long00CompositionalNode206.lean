/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode203
import Proofs.RadenkovicGutmanD40Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[154,0],[0,0]],[[0,0],[0,0]],[[2204,0],[0,0]],[[0,0],[0,0]],[[14402,0],[0,0]],[[0,0],[0,0]],[[52552,0],[0,0]],[[0,0],[0,0]],[[114968,2],[2,0]],[[0,0],[0,0]],[[153100,136],[136,0]],[[0,0],[0,0]],[[120914,924],[924,0]],[[0,0],[0,0]],[[52198,2208],[2208,0]],[[0,0],[0,0]],[[9978,2018],[2018,0]],[[0,0],[0,0]],[[360,600],[600,2]],[[0],[0,0]],[[0],[0,40]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
