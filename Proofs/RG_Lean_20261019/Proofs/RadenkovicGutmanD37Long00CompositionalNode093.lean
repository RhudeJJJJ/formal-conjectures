/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode033
import Proofs.RadenkovicGutmanD37Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1369]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,32856],[0,32856,74]],[[0,0,0],[0,0,0],[0,0]],[[-110889,-73926,184815],[-73926,714618,102638],[184815,102638]],[[0,0,0],[0,0,0],[0,0]],[[-3036960,2809188,1114884],[2809188,4245972,107596],[1114884,107596]],[[0,0,0],[0,0,0],[0,0]],[[-13003983,27509796,2791872],[27509796,10441918,44326],[2791872,44326]],[[0,0,0],[0,0,0],[0,0]],[[31454070,109827322,3787394],[109827322,13895572,6660],[3787394,6660]],[[0,0,0],[0,0,0],[0,0]],[[448555181,252453516,3043102],[252453516,10956736,148],[3043102,148]],[[0,0,0],[0,0],[0]],[[1856735480,376747468,1486586],[376747468,5261844],[1486586]],[[0,0,0],[0,0],[0]],[[4573430362,386115128,434824],[386115128,1517518],[434824]],[[0,0,0],[0,0],[0]],[[7735284824,279220426,70966],[279220426,245532],[70966]],[[0,0,0],[0,0],[0]],[[9533576066,143820406,5291],[143820406,18426],[5291]],[[0,0,0],[0,0],[0]],[[8824333796,52505442,74],[52505442,296],[74]],[[0,0],[0]],[[6230834928,13308160],[13308160]],[[0,0],[0]],[[3377904344,2241460],[2241460]],[[0,0],[0]],[[1404844009,229844],[229844]],[[0,0],[0]],[[444655344,11766],[11766]],[[0,0],[0]],[[105348546,148],[148]],[[0]],[[18151312]],[[0]],[[2165129]],[[0]],[[163540]],[[0]],[[6475]],[[0]],[[74]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
