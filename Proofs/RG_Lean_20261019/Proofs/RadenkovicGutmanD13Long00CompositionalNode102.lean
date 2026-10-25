/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode100
import Proofs.RadenkovicGutmanD13Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,169]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-1521],[0,-3042,4914],[-1521,4914,26]],[[0,0,0],[0,0,0],[0,0]],[[-13689,-51597,17355],[-51597,93678,16692],[17355,16692]],[[0,0,0],[0,0,0],[0,0]],[[-639522,102843,148265],[102843,664378,18668],[148265,18668]],[[0,0,0],[0,0,0],[0,0]],[[-3591081,3408561,423826],[3408561,1788098,8216],[423826,8216]],[[0,0,0],[0,0,0],[0,0]],[[2428296,17145024,625404],[17145024,2544516,1378],[625404,1378]],[[0,0,0],[0,0,0],[0,0]],[[92482637,44489237,535548],[44489237,2122796,52],[535548,52]],[[0,0,0],[0,0],[0]],[[434152576,72065747,276003],[72065747,1072890],[276003]],[[0,0,0],[0,0],[0]],[[1143393862,78551824,84942],[78551824,325546],[84942]],[[0,0,0],[0,0],[0]],[[2022121010,59655869,14703],[59655869,55874],[14703]],[[0,0,0],[0,0],[0]],[[2572978824,31999331,1209],[31999331,4602],[1209]],[[0,0,0],[0,0],[0]],[[2437908512,12100062,26],[12100062,104],[26]],[[0,0],[0]],[[1751551490,3168035],[3168035]],[[0,0],[0]],[[962055822,551551],[551551]],[[0,0],[0]],[[404168453,58877],[58877]],[[0,0],[0]],[[128977368,3224],[3224]],[[0,0],[0]],[[30780906,52],[52]],[[0]],[[5343390]],[[0]],[[643383]],[[0]],[[49322]],[[0]],[[2015]],[[0]],[[26]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
