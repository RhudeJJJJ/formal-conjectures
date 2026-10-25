/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode067
import Proofs.RadenkovicGutmanD13Long00CompositionalNode069
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e070 : NestedArithmetic.Expr 3 := .plus e067 e069
noncomputable def p070 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,169]],[[0,0],[0,0,0],[0,0,0]],[[0,0,1521],[0,3042,3354],[1521,3354,536]],[[0,0,0],[0,0,0],[0,0,0]],[[-13689,53001,35763],[53001,102936,19424],[35763,19424,4]],[[0,0,0],[0,0,0],[0,0]],[[166266,1109295,236401],[1109295,736454,36252],[236401,36252]],[[0,0,0],[0,0,0],[0,0]],[[6695109,8562411,726630],[8562411,2343364,28872],[726630,28872]],[[0,0,0],[0,0,0],[0,0]],[[66392754,35121286,1243180],[35121286,4111164,9922],[1243180,9922]],[[0,0,0],[0,0,0],[0,0]],[[348826883,88913159,1284088],[88913159,4353268,1240],[1284088,1240]],[[0,0,0],[0,0,0],[0,0]],[[1168068232,150178515,829305],[150178515,2888306,8],[829305,8]],[[0,0,0],[0,0],[0]],[[2717408226,176903220,336270],[176903220,1205580],[336270]],[[0,0,0],[0,0],[0]],[[4613571922,149016251,83161],[149016251,307350],[83161]],[[0,0,0],[0,0],[0]],[[5893234490,90840317,11517],[90840317,43924],[11517]],[[0,0,0],[0,0],[0]],[[5773845768,40114492,704],[40114492,2772],[704]],[[0,0,0],[0,0],[0]],[[4389343146,12699165,4],[12699165,16],[4]],[[0,0],[0]],[[2603808466,2809723],[2809723]],[[0,0],[0]],[[1205796563,413371],[413371]],[[0,0],[0]],[[433772352,36606],[36606]],[[0,0],[0]],[[119872638,1532],[1532]],[[0,0],[0]],[[24953774,8],[8]],[[0]],[[3787901]],[[0]],[[396790]],[[0]],[[25881]],[[0]],[[828]],[[0]],[[4]]]
theorem step070 : p070=NestedHorner.add p067 p069 := by decide +kernel
#print axioms step070
theorem h070 : NestedArithmetic.compile e070=p070 := StagedExprCompile.compile_plus e070 e067 e069 p067 p069 p070 rfl h067 h069 step070
#print axioms h070
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
