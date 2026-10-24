/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode111
import Proofs.RadenkovicGutmanD3Long00StagedUNode112
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .plus e111 e112
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,9]],[[0,0],[0,0,0],[0,0]],[[0,0,81],[0,0,162],[81,162]],[[0,0,0],[0,0,0],[0,0]],[[729,1458,1431],[1458,2916,432],[1431,432]],[[0,0,0],[0,0,0],[0,0]],[[25758,29646,6273],[29646,15552,396],[6273,396]],[[0,0,0],[0,0,0],[0,0]],[[340443,185166,12870],[185166,34992,144],[12870,144]],[[0,0,0],[0,0,0],[0,0]],[[2226474,597024,14796],[597024,43200,18],[14796,18]],[[0,0,0],[0,0],[0]],[[8731269,1183158,10224],[1183158,31896],[10224]],[[0,0,0],[0,0],[0]],[[22829940,1563750,4329],[1563750,14400],[4329]],[[0,0,0],[0,0],[0]],[[42358878,1438164,1098],[1438164,3888],[1098]],[[0,0,0],[0,0],[0]],[[57965202,939888,153],[939888,576],[153]],[[0,0,0],[0,0],[0]],[[59951808,439110,9],[439110,36],[9]],[[0,0],[0]],[[47576880,145530],[145530]],[[0,0],[0]],[[29204640,33390],[33390]],[[0,0],[0]],[[13895838,5040],[5040]],[[0,0],[0]],[[5105709,450],[450]],[[0,0],[0]],[[1433484,18],[18]],[[0]],[[301590]],[[0]],[[45990]],[[0]],[[4797]],[[0]],[[306]],[[0]],[[9]]]
theorem step113 : p113=NestedHorner.add p111 p112 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := by
  change NestedHorner.add (NestedArithmetic.compile e111) (NestedArithmetic.compile e112)=p113
  rw [h111,h112]
  exact step113.symm
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
