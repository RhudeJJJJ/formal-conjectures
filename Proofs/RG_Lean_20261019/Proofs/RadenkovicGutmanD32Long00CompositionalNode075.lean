/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode033
import Proofs.RadenkovicGutmanD32Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1024]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,18432],[0,18432]],[[0,0,0],[0,0,0],[0,0]],[[-82944,0,82944],[0,331776,49152],[82944,49152]],[[0,0,0],[0,0,0],[0,0]],[[-1437696,1492992,442368],[1492992,1769472,45056],[442368,45056]],[[0,0,0],[0,0,0],[0,0]],[[-4396032,11943936,995328],[11943936,3981312,16384],[995328,16384]],[[0,0,0],[0,0,0],[0,0]],[[20889600,42799104,1228800],[42799104,4915200,2048],[1228800,2048]],[[0,0,0],[0,0],[0]],[[199089152,90685440,907264],[90685440,3629056],[907264]],[[0,0,0],[0,0],[0]],[[734928896,126351360,409600],[126351360,1638400],[409600]],[[0,0,0],[0,0],[0]],[[1678923776,121798656,110592],[121798656,442368],[110592]],[[0,0,0],[0,0],[0]],[[2673676288,83222528,16384],[83222528,65536],[16384]],[[0,0,0],[0,0],[0]],[[3127513088,40599552,1024],[40599552,4096],[1024]],[[0,0],[0]],[[2760839168,14039040],[14039040]],[[0,0],[0]],[[1864859648,3358720],[3358720]],[[0,0],[0]],[[968826880,528384],[528384]],[[0,0],[0]],[[386325504,49152],[49152]],[[0,0],[0]],[[117129216,2048],[2048]],[[0]],[[26499072]],[[0]],[[4329472]],[[0]],[[482304]],[[0]],[[32768]],[[0]],[[1024]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
