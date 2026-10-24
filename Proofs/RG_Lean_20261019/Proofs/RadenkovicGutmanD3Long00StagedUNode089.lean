/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode088
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .scaled (-1) e088
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,27],[0,27]],[[0,0,0],[0,0,0],[0,0]],[[0,243,405],[243,1296,135],[405,135]],[[0,0,0],[0,0,0],[0,0]],[[4374,15228,3267],[15228,10260,222],[3267,222]],[[0,0,0],[0,0,0],[0,0]],[[154548,147258,10602],[147258,32868,159],[10602,159]],[[0,0,0],[0,0,0],[0,0]],[[1633932,660132,18189],[660132,56268,51],[18189,51]],[[0,0,0],[0,0,0],[0,0]],[[8969616,1735818,18258],[1735818,57048,6],[18258,6]],[[0,0,0],[0,0],[0]],[[30794958,2965122,11187],[2965122,35748],[11187]],[[0,0,0],[0,0],[0]],[[72440172,3471804,4218],[3471804,13956],[4218]],[[0,0,0],[0,0],[0]],[[123041856,2869521,951],[2869521,3300],[951]],[[0,0,0],[0,0],[0]],[[155888970,1698057,117],[1698057,432],[117]],[[0,0,0],[0,0],[0]],[[150382434,720945,6],[720945,24],[6]],[[0,0],[0]],[[111843834,217392],[217392]],[[0,0],[0]],[[64532088,45351],[45351]],[[0,0],[0]],[[28908852,6210],[6210]],[[0,0],[0]],[[10006986,501],[501]],[[0,0],[0]],[[2646480,18],[18]],[[0]],[[524016]],[[0]],[[75090]],[[0]],[[7344]],[[0]],[[438]],[[0]],[[12]]]
theorem step089 : p089=NestedHorner.scale (-1) p088 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := by
  change NestedHorner.scale (-1) (NestedArithmetic.compile e088)=p089
  rw [h088]
  exact step089.symm
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
