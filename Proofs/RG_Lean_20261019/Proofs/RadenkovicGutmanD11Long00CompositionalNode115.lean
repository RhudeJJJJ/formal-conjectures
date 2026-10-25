/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode113
import Proofs.RadenkovicGutmanD11Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,121]],[[0,0],[0,0,0],[0,0]],[[0,0,1089],[0,0,2178],[1089,2178]],[[0,0,0],[0,0,0],[0,0]],[[9801,19602,19239],[19602,39204,5808],[19239,5808]],[[0,0,0],[0,0,0],[0,0]],[[346302,398574,84337],[398574,209088,5324],[84337,5324]],[[0,0,0],[0,0,0],[0,0]],[[4577067,2489454,173030],[2489454,470448,1936],[173030,1936]],[[0,0,0],[0,0,0],[0,0]],[[29933706,8026656,198924],[8026656,580800,242],[198924,242]],[[0,0,0],[0,0],[0]],[[117387061,15906902,137456],[15906902,428824],[137456]],[[0,0,0],[0,0],[0]],[[306935860,21023750,58201],[21023750,193600],[58201]],[[0,0,0],[0,0],[0]],[[569491582,19335316,14762],[19335316,52272],[14762]],[[0,0,0],[0,0],[0]],[[779309938,12636272,2057],[12636272,7744],[2057]],[[0,0,0],[0,0],[0]],[[806018752,5903590,121],[5903590,484],[121]],[[0,0],[0]],[[639644720,1956570],[1956570]],[[0,0],[0]],[[392640160,448910],[448910]],[[0,0],[0]],[[186821822,67760],[67760]],[[0,0],[0]],[[68643421,6050],[6050]],[[0,0],[0]],[[19272396,242],[242]],[[0]],[[4054710]],[[0]],[[618310]],[[0]],[[64493]],[[0]],[[4114]],[[0]],[[121]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
