/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode193
import Proofs.RadenkovicGutmanD20Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[130,0],[0,0]],[[0,0],[0,0]],[[1688,0],[0,0]],[[0,0],[0,0]],[[10038,0],[0,0]],[[0,0],[0,0]],[[33172,0],[0,0]],[[0,0],[0,0]],[[65112,2],[2,0]],[[0,0],[0,0]],[[76708,76],[76,0]],[[0,0],[0,0]],[[52374,484],[484,0]],[[0,0],[0,0]],[[18466,1128],[1128,0]],[[0,0],[0,0]],[[2202,1018],[1018,0]],[[0,0],[0,0]],[[-180,300],[300,2]],[[0],[0,0]],[[0],[0,20]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
