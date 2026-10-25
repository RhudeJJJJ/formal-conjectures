/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode043
import Proofs.RadenkovicGutmanD13Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e043 e066
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-507],[0,-507,286]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-4563,-7605],[-4563,-25272,4589],[-7605,4589,44]],[[0,0,0],[0,0,0],[0,0]],[[-113724,-313092,-20397],[-313092,-42264,18914],[-20397,18914]],[[0,0,0],[0,0,0],[0,0]],[[-3804084,-2254482,52522],[-2254482,315804,22249],[52522,22249]],[[0,0,0],[0,0,0],[0,0]],[[-35915454,-6711316,299275],[-6711316,1303256,10165],[299275,10165]],[[0,0,0],[0,0,0],[0,0]],[[-173641860,-8853558,541734],[-8853558,2151600,1822],[541734,1822]],[[0,0,0],[0,0,0],[0,0]],[[-516468336,527798,515041],[527798,1942092,88],[515041,88]],[[0,0,0],[0,0],[0]],[[-1022510084,20762668,284294],[20762668,1036508],[284294]],[[0,0,0],[0,0],[0]],[[-1387141204,36248263,92545],[36248263,330560],[92545]],[[0,0,0],[0,0],[0]],[[-1267543986,34818095,17011],[34818095,60384],[17011]],[[0,0,0],[0,0],[0]],[[-687482206,21687031,1536],[21687031,5556],[1536]],[[0,0,0],[0,0],[0]],[[-52828346,9151992,44],[9151992,176],[44]],[[0,0],[0]],[[277999696,2624729],[2624729]],[[0,0],[0]],[[287555236,498354],[498354]],[[0,0],[0]],[[167010860,58739],[58739]],[[0,0],[0]],[[65909112,3734],[3734]],[[0,0],[0]],[[18448924,88],[88]],[[0]],[[3660806]],[[0]],[[500206]],[[0]],[[44122]],[[0]],[[2198]],[[0]],[[44]]]
theorem step071 : p071=NestedArithmetic.mul p043 p066 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e043 e066 p043 p066 p071 rfl h043 h066 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
