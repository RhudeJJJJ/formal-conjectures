/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode070
import Proofs.RadenkovicGutmanD21Long00CompositionalNode082
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e083 : NestedArithmetic.Expr 3 := .plus e070 e082
noncomputable def p083 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,504],[0,504,1528]],[[0,0,0],[0,0,0],[0,0,0]],[[0,4536,20412],[4536,47160,30192],[20412,30192,4]],[[0,0,0],[0,0,0],[0,0]],[[-66744,685260,297648],[685260,891012,78288],[297648,78288]],[[0,0,0],[0,0,0],[0,0]],[[3581928,9494280,1247328],[9494280,3967904,71288],[1247328,71288]],[[0,0,0],[0,0,0],[0,0]],[[65465604,51888876,2509728],[51888876,8263716,25968],[2509728,25968]],[[0,0,0],[0,0,0],[0,0]],[[457576932,155571204,2854728],[155571204,9682696,3288],[2854728,3288]],[[0,0,0],[0,0,0],[0,0]],[[1821063052,293319284,1960048],[293319284,6848448,8],[1960048,8]],[[0,0,0],[0,0],[0]],[[4759355288,372791776,827012],[372791776,2978656],[827012]],[[0,0,0],[0,0],[0]],[[8783496248,331631088,209632],[331631088,778724],[209632]],[[0,0,0],[0,0],[0]],[[11941302560,210429924,29332],[210429924,112432],[29332]],[[0,0,0],[0,0],[0]],[[12273304052,95725332,1760],[95725332,6964],[1760]],[[0,0,0],[0,0],[0]],[[9687027624,30968812,4],[30968812,16],[4]],[[0,0],[0]],[[5920018368,6954332],[6954332]],[[0,0],[0]],[[2807289048,1030960],[1030960]],[[0,0],[0]],[[1029065460,90988],[90988]],[[0,0],[0]],[[288560968,3676],[3676]],[[0,0],[0]],[[60711624,8],[8]],[[0]],[[9274528]],[[0]],[[972036]],[[0]],[[62736]],[[0]],[[1916]],[[0]],[[4]]]
theorem step083 : p083=NestedHorner.add p070 p082 := by decide +kernel
#print axioms step083
theorem h083 : NestedArithmetic.compile e083=p083 := StagedExprCompile.compile_plus e083 e070 e082 p070 p082 p083 rfl h070 h082 step083
#print axioms h083
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
