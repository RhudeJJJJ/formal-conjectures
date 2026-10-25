/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1936]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-34848,34848],[0,34848]],[[0,0,0],[0,0,0],[0,0]],[[156816,-313632,156816],[-313632,325248,92928],[156816,92928]],[[0,0,0],[0,0,0],[0,0]],[[-104544,-731808,836352],[-731808,2319328,85184],[836352,85184]],[[0,0,0],[0,0,0],[0,0]],[[-5802192,5331744,1881792],[5331744,5753792,30976],[1881792,30976]],[[0,0,0],[0,0,0],[0,0]],[[-15972000,33407616,2323200],[33407616,7573632,3872],[2323200,3872]],[[0,0,0],[0,0],[0]],[[33618640,88393888,1715296],[88393888,5893184],[1715296]],[[0,0,0],[0,0],[0]],[[318983104,141386080,774400],[141386080,2783968],[774400]],[[0,0,0],[0,0],[0]],[[996602464,151186112,209088],[151186112,782144],[209088]],[[0,0,0],[0,0],[0]],[[1916279904,112504832,30976],[112504832,120032],[30976]],[[0,0,0],[0,0],[0]],[[2579108224,59059616,1936],[59059616,7744],[1936]],[[0,0],[0]],[[2557517952,21780000],[21780000]],[[0,0],[0]],[[1913681792,5517600],[5517600]],[[0,0],[0]],[[1091226400,913792],[913792]],[[0,0],[0]],[[474391632,89056],[89056]],[[0,0],[0]],[[155971904,3872],[3872]],[[0]],[[38096608]],[[0]],[[6694688]],[[0]],[[799568]],[[0]],[[58080]],[[0]],[[1936]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
