/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode033
import Proofs.RadenkovicGutmanD13Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,169]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,3042],[0,3042]],[[0,0,0],[0,0,0],[0,0]],[[-13689,0,13689],[0,54756,8112],[13689,8112]],[[0,0,0],[0,0,0],[0,0]],[[-237276,246402,73008],[246402,292032,7436],[73008,7436]],[[0,0,0],[0,0,0],[0,0]],[[-725517,1971216,164268],[1971216,657072,2704],[164268,2704]],[[0,0,0],[0,0,0],[0,0]],[[3447600,7063524,202800],[7063524,811200,338],[202800,338]],[[0,0,0],[0,0],[0]],[[32857487,14966640,149734],[14966640,598936],[149734]],[[0,0,0],[0,0],[0]],[[121291976,20852910,67600],[20852910,270400],[67600]],[[0,0,0],[0,0],[0]],[[277088006,20101536,18252],[20101536,73008],[18252]],[[0,0,0],[0,0],[0]],[[441261028,13734968,2704],[13734968,10816],[2704]],[[0,0,0],[0,0],[0]],[[516161828,6700512,169],[6700512,676],[169]],[[0,0],[0]],[[455646308,2316990],[2316990]],[[0,0],[0]],[[307774688,554320],[554320]],[[0,0],[0]],[[159894280,87204],[87204]],[[0,0],[0]],[[63758799,8112],[8112]],[[0,0],[0]],[[19330896,338],[338]],[[0]],[[4373382]],[[0]],[[714532]],[[0]],[[79599]],[[0]],[[5408]],[[0]],[[169]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
