/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode070
import Proofs.RadenkovicGutmanD18Long00CompositionalNode082
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e083 : NestedArithmetic.Expr 3 := .plus e070 e082
noncomputable def p083 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,432],[0,432,1096]],[[0,0,0],[0,0,0],[0,0,0]],[[0,3888,15552],[3888,36576,22032],[15552,22032,4]],[[0,0,0],[0,0,0],[0,0]],[[-39528,523584,220968],[523584,661152,56856],[220968,56856]],[[0,0,0],[0,0,0],[0,0]],[[2855196,7113312,919620],[7113312,2918768,51728],[919620,51728]],[[0,0,0],[0,0,0],[0,0]],[[49955400,38578392,1844784],[38578392,6057792,18864],[1844784,18864]],[[0,0,0],[0,0,0],[0,0]],[[344661132,115204992,2095104],[115204992,7086592,2400],[2095104,2400]],[[0,0,0],[0,0,0],[0,0]],[[1362986392,216701792,1437376],[216701792,5009088,8],[1437376,8]],[[0,0,0],[0,0],[0]],[[3548759036,275009440,606392],[275009440,2178880],[606392]],[[0,0,0],[0,0],[0]],[[6533129360,244418472,153808],[244418472,570176],[153808]],[[0,0,0],[0,0],[0]],[[8866650680,155009424,21568],[155009424,82528],[21568]],[[0,0,0],[0,0],[0]],[[9102012368,70501968,1304],[70501968,5152],[1304]],[[0,0,0],[0,0],[0]],[[7177742256,22813120,4],[22813120,16],[4]],[[0,0],[0]],[[4383920784,5126456],[5126456]],[[0,0],[0]],[[2078140512,761152],[761152]],[[0,0],[0]],[[761698488,67408],[67408]],[[0,0],[0]],[[213622588,2752],[2752]],[[0,0],[0]],[[44967984,8],[8]],[[0]],[[6876664]],[[0]],[[722184]],[[0]],[[46812]],[[0]],[[1448]],[[0]],[[4]]]
theorem step083 : p083=NestedHorner.add p070 p082 := by decide +kernel
#print axioms step083
theorem h083 : NestedArithmetic.compile e083=p083 := StagedExprCompile.compile_plus e083 e070 e082 p070 p082 p083 rfl h070 h082 step083
#print axioms h083
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
