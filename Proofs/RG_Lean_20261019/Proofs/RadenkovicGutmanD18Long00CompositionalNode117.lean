/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode112
import Proofs.RadenkovicGutmanD18Long00CompositionalNode116
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e117 : NestedArithmetic.Expr 3 := .plus e112 e116
noncomputable def p117 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,432],[0,432,1096]],[[0,0,0],[0,0,0],[0,0,0]],[[0,3888,15552],[3888,15840,22032],[15552,22032,4]],[[0,0,0],[0,0,0],[0,0]],[[193752,371952,220968],[371952,482088,56856],[220968,56856]],[[0,0,0],[0,0,0],[0,0]],[[5854788,5458968,919620],[5458968,2313824,51728],[919620,51728]],[[0,0,0],[0,0,0],[0,0]],[[67721616,30911256,1844784],[30911256,5021640,18864],[1844784,18864]],[[0,0,0],[0,0,0],[0,0]],[[410667276,95200152,2095104],[95200152,6096592,2400],[2095104,2400]],[[0,0,0],[0,0,0],[0,0]],[[1538462272,183819104,1437376],[183819104,4465056,8],[1437376,8]],[[0,0,0],[0,0],[0]],[[3903881108,238993960,606392],[238993960,2010256],[606392]],[[0,0,0],[0,0],[0]],[[7093199360,217402056,153808],[217402056,543752],[153808]],[[0,0,0],[0,0],[0]],[[9558534392,141024432,21568],[141024432,81232],[21568]],[[0,0,0],[0,0],[0]],[[9771147176,65566944,1304],[65566944,5224],[1304]],[[0,0,0],[0,0],[0]],[[7683773088,21674296,4],[21674296,16],[4]],[[0,0],[0]],[[4682753184,4972376],[4972376]],[[0,0],[0]],[[2215546752,753160],[753160]],[[0,0],[0]],[[810588432,67984],[67984]],[[0,0],[0]],[[226928116,2824],[2824]],[[0,0],[0]],[[47683104,8],[8]],[[0]],[[7278424]],[[0]],[[762864]],[[0]],[[49332]],[[0]],[[1520]],[[0]],[[4]]]
theorem step117 : p117=NestedHorner.add p112 p116 := by decide +kernel
#print axioms step117
theorem h117 : NestedArithmetic.compile e117=p117 := StagedExprCompile.compile_plus e117 e112 e116 p112 p116 p117 rfl h112 h116 step117
#print axioms h117
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
