/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode033
import Proofs.RadenkovicGutmanD39Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1521]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,27378],[0,27378]],[[0,0,0],[0,0,0],[0,0]],[[-123201,0,123201],[0,492804,73008],[123201,73008]],[[0,0,0],[0,0,0],[0,0]],[[-2135484,2217618,657072],[2217618,2628288,66924],[657072,66924]],[[0,0,0],[0,0,0],[0,0]],[[-6529653,17740944,1478412],[17740944,5913648,24336],[1478412,24336]],[[0,0,0],[0,0,0],[0,0]],[[31028400,63571716,1825200],[63571716,7300800,3042],[1825200,3042]],[[0,0,0],[0,0],[0]],[[295717383,134699760,1347606],[134699760,5390424],[1347606]],[[0,0,0],[0,0],[0]],[[1091627784,187676190,608400],[187676190,2433600],[608400]],[[0,0,0],[0,0],[0]],[[2493792054,180913824,164268],[180913824,657072],[164268]],[[0,0,0],[0,0],[0]],[[3971349252,123614712,24336],[123614712,97344],[24336]],[[0,0,0],[0,0],[0]],[[4645456452,60304608,1521],[60304608,6084],[1521]],[[0,0],[0]],[[4100816772,20852910],[20852910]],[[0,0],[0]],[[2769972192,4988880],[4988880]],[[0,0],[0]],[[1439048520,784836],[784836]],[[0,0],[0]],[[573829191,73008],[73008]],[[0,0],[0]],[[173978064,3042],[3042]],[[0]],[[39360438]],[[0]],[[6430788]],[[0]],[[716391]],[[0]],[[48672]],[[0]],[[1521]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
