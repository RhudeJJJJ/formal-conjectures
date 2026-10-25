/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode051
import Proofs.RadenkovicGutmanD24Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,576]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,13824],[0,13824,48]],[[0,0,0],[0,0,0],[0,0]],[[-46656,31104,77760],[31104,311904,43488],[77760,43488]],[[0,0,0],[0,0,0],[0,0]],[[-244944,2091744,470448],[2091744,1889280,46080],[470448,46080]],[[0,0,0],[0,0,0],[0,0]],[[11474784,17244576,1181952],[17244576,4753248,19392],[1181952,19392]],[[0,0,0],[0,0,0],[0,0]],[[136986768,66089376,1609920],[66089376,6483648,3072],[1609920,3072]],[[0,0,0],[0,0,0],[0,0]],[[723256992,150071040,1300608],[150071040,5245056,96],[1300608,96]],[[0,0,0],[0,0],[0]],[[2313714288,223143072,640416],[223143072,2585664],[640416]],[[0,0,0],[0,0],[0]],[[5027817792,228374304,189696],[228374304,766560],[189696]],[[0,0,0],[0,0],[0]],[[7865934240,164933184,31680],[164933184,128064],[31680]],[[0,0,0],[0,0],[0]],[[9161484384,84801408,2496],[84801408,10080],[2496]],[[0,0,0],[0,0],[0]],[[8103230976,30893088,48],[30893088,192],[48]],[[0,0],[0]],[[5502935040,7814880],[7814880]],[[0,0],[0]],[[2881228800,1315104],[1315104]],[[0,0],[0]],[[1160709216,135168],[135168]],[[0,0],[0]],[[356658672,7008],[7008]],[[0,0],[0]],[[82173888,96],[96]],[[0]],[[13785120]],[[0]],[[1601760]],[[0]],[[117744]],[[0]],[[4512]],[[0]],[[48]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
