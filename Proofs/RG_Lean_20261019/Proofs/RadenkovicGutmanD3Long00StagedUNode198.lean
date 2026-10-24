/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode195
import Proofs.RadenkovicGutmanD3Long00StagedUNode197
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .plus e195 e197
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[49,0],[0,0]],[[0,0],[0,0]],[[469,0],[0,0]],[[0,0],[0,0]],[[2372,0],[0,0]],[[0,0],[0,0]],[[7057,0],[0,0]],[[0,0],[0,0]],[[12828,2],[2,0]],[[0,0],[0,0]],[[14212,25],[25,0]],[[0,0],[0,0]],[[9200,110],[110,0]],[[0,0],[0,0]],[[3087,210],[210,0]],[[0,0],[0,0]],[[351,168],[168,0]],[[0,0],[0,0]],[[-27,45],[45,2]],[[0],[0,0]],[[0],[0,3]]]
theorem step198 : p198=NestedHorner.add p195 p197 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_plus e198 e195 e197 p195 p197 p198 rfl h195 h197 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
