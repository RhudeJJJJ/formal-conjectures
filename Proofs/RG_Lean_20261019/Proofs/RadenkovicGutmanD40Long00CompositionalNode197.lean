/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode193
import Proofs.RadenkovicGutmanD40Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[230,0],[0,0]],[[0,0],[0,0]],[[3188,0],[0,0]],[[0,0],[0,0]],[[19438,0],[0,0]],[[0,0],[0,0]],[[65072,0],[0,0]],[[0,0],[0,0]],[[128712,2],[2,0]],[[0,0],[0,0]],[[152388,136],[136,0]],[[0,0],[0,0]],[[104414,924],[924,0]],[[0,0],[0,0]],[[36926,2208],[2208,0]],[[0,0],[0,0]],[[4422,2018],[2018,0]],[[0,0],[0,0]],[[-360,600],[600,2]],[[0],[0,0]],[[0],[0,40]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
