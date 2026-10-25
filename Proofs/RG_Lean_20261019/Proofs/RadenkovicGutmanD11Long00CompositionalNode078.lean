/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode075
import Proofs.RadenkovicGutmanD11Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,121]],[[0,0],[0,0,0],[0,0]],[[0,0,1089],[0,2178,2178],[1089,2178]],[[0,0,0],[0,0,0],[0,0]],[[-9801,35937,19239],[35937,58080,5808],[19239,5808]],[[0,0,0],[0,0,0],[0,0]],[[124146,578259,84337],[578259,273218,5324],[84337,5324]],[[0,0,0],[0,0,0],[0,0]],[[3498957,3331251,173030],[3331251,581284,1936],[173030,1936]],[[0,0,0],[0,0,0],[0,0]],[[26964366,10254266,198924],[10254266,688248,242],[198924,242]],[[0,0,0],[0,0],[0]],[[112195919,19636243,137456],[19636243,489324],[137456]],[[0,0,0],[0,0],[0]],[[300842300,25207567,58201],[25207567,213202],[58201]],[[0,0,0],[0,0],[0]],[[564548490,22576180,14762],[22576180,55660],[14762]],[[0,0,0],[0,0],[0]],[[776507578,14390651,2057],[14390651,7986],[2057]],[[0,0,0],[0,0],[0]],[[804912570,6565097,121],[6565097,484],[121]],[[0,0],[0]],[[639347060,2126696],[2126696]],[[0,0],[0]],[[392588130,477345],[477345]],[[0,0],[0]],[[186816498,70543],[70543]],[[0,0],[0]],[[68643179,6171],[6171]],[[0,0],[0]],[[19272396,242],[242]],[[0]],[[4054710]],[[0]],[[618310]],[[0]],[[64493]],[[0]],[[4114]],[[0]],[[121]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
