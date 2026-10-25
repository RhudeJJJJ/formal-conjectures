/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,169]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-3042,3042],[0,3042]],[[0,0,0],[0,0,0],[0,0]],[[13689,-27378,13689],[-27378,28392,8112],[13689,8112]],[[0,0,0],[0,0,0],[0,0]],[[-9126,-63882,73008],[-63882,202462,7436],[73008,7436]],[[0,0,0],[0,0,0],[0,0]],[[-506493,465426,164268],[465426,502268,2704],[164268,2704]],[[0,0,0],[0,0,0],[0,0]],[[-1394250,2916264,202800],[2916264,661128,338],[202800,338]],[[0,0,0],[0,0],[0]],[[2934685,7716202,149734],[7716202,514436],[149734]],[[0,0,0],[0,0],[0]],[[27845116,12342070,67600],[12342070,243022],[67600]],[[0,0,0],[0,0],[0]],[[86996806,13197548,18252],[13197548,68276],[18252]],[[0,0,0],[0,0],[0]],[[167278566,9820928,2704],[9820928,10478],[2704]],[[0,0,0],[0,0],[0]],[[225139096,5155514,169],[5155514,676],[169]],[[0,0],[0]],[[223254408,1901250],[1901250]],[[0,0],[0]],[[167051768,481650],[481650]],[[0,0],[0]],[[95256850,79768],[79768]],[[0,0],[0]],[[41411253,7774],[7774]],[[0,0],[0]],[[13615316,338],[338]],[[0]],[[3325582]],[[0]],[[584402]],[[0]],[[69797]],[[0]],[[5070]],[[0]],[[169]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
