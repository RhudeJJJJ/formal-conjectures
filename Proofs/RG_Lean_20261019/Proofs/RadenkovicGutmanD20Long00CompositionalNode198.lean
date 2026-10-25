/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode197
import Proofs.RadenkovicGutmanD20Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[130,0],[0,0]],[[0,0],[0,0]],[[1688,0],[0,0]],[[0,0],[0,0]],[[10038,0],[0,0]],[[0,0],[0,0]],[[33172,0],[0,0]],[[0,0],[0,0]],[[65112,2],[2,0]],[[0,0],[0,0]],[[76708,76],[76,0]],[[0,0],[0,0]],[[52374,484],[484,0]],[[0,0],[0,0]],[[18466,1128],[1128,0]],[[0,0],[0,0]],[[2202,1018],[1018,0]],[[0,0],[0,0]],[[-180,300],[300,2]],[[0],[0,0]],[[0],[0,20]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
