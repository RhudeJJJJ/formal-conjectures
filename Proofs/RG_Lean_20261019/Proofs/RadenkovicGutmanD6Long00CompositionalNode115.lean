/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode113
import Proofs.RadenkovicGutmanD6Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,36]],[[0,0],[0,0,0],[0,0]],[[0,0,324],[0,0,648],[324,648]],[[0,0,0],[0,0,0],[0,0]],[[2916,5832,5724],[5832,11664,1728],[5724,1728]],[[0,0,0],[0,0,0],[0,0]],[[103032,118584,25092],[118584,62208,1584],[25092,1584]],[[0,0,0],[0,0,0],[0,0]],[[1361772,740664,51480],[740664,139968,576],[51480,576]],[[0,0,0],[0,0,0],[0,0]],[[8905896,2388096,59184],[2388096,172800,72],[59184,72]],[[0,0,0],[0,0],[0]],[[34925076,4732632,40896],[4732632,127584],[40896]],[[0,0,0],[0,0],[0]],[[91319760,6255000,17316],[6255000,57600],[17316]],[[0,0,0],[0,0],[0]],[[169435512,5752656,4392],[5752656,15552],[4392]],[[0,0,0],[0,0],[0]],[[231860808,3759552,612],[3759552,2304],[612]],[[0,0,0],[0,0],[0]],[[239807232,1756440,36],[1756440,144],[36]],[[0,0],[0]],[[190307520,582120],[582120]],[[0,0],[0]],[[116818560,133560],[133560]],[[0,0],[0]],[[55583352,20160],[20160]],[[0,0],[0]],[[20422836,1800],[1800]],[[0,0],[0]],[[5733936,72],[72]],[[0]],[[1206360]],[[0]],[[183960]],[[0]],[[19188]],[[0]],[[1224]],[[0]],[[36]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
