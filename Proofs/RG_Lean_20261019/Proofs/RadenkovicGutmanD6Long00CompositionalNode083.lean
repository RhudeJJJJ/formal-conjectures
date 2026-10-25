/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode070
import Proofs.RadenkovicGutmanD6Long00CompositionalNode082
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e083 : NestedArithmetic.Expr 3 := .plus e070 e082
noncomputable def p083 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,144],[0,144,88]],[[0,0,0],[0,0,0],[0,0,0]],[[0,1296,2592],[1296,7200,2352],[2592,2352,4]],[[0,0,0],[0,0,0],[0,0]],[[11016,90720,28728],[90720,87312,5688],[28728,5688]],[[0,0,0],[0,0,0],[0,0]],[[686988,1030320,110628],[1030320,347984,5168],[110628,5168]],[[0,0,0],[0,0,0],[0,0]],[[8734824,5158776,214608],[5158776,692976,1968],[214608,1968]],[[0,0,0],[0,0,0],[0,0]],[[53447052,14757264,240288],[14757264,797536,288],[240288,288]],[[0,0,0],[0,0,0],[0,0]],[[198291832,27075584,164608],[27075584,563328,8],[164608,8]],[[0,0,0],[0,0],[0]],[[496510028,33875536,70232],[33875536,248416],[70232]],[[0,0,0],[0,0],[0]],[[890958608,29905608,18352],[29905608,67184],[18352]],[[0,0,0],[0,0],[0]],[[1188584120,18957744,2752],[18957744,10432],[2752]],[[0,0,0],[0,0],[0]],[[1206408032,8673552,200],[8673552,784],[200]],[[0,0,0],[0,0],[0]],[[944979984,2845072,4],[2845072,16],[4]],[[0,0],[0]],[[575592048,655352],[655352]],[[0,0],[0]],[[273181728,101680],[101680]],[[0,0],[0]],[[100685880,9808],[9808]],[[0,0],[0]],[[28547788,496],[496]],[[0,0],[0]],[[6120624,8],[8]],[[0]],[[964408]],[[0]],[[106536]],[[0]],[[7596]],[[0]],[[296]],[[0]],[[4]]]
theorem step083 : p083=NestedHorner.add p070 p082 := by decide +kernel
#print axioms step083
theorem h083 : NestedArithmetic.compile e083=p083 := StagedExprCompile.compile_plus e083 e070 e082 p070 p082 p083 rfl h070 h082 step083
#print axioms h083
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
