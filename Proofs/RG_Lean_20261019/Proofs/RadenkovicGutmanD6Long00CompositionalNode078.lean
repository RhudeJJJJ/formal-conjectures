/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode075
import Proofs.RadenkovicGutmanD6Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,36]],[[0,0],[0,0,0],[0,0]],[[0,0,324],[0,648,648],[324,648]],[[0,0,0],[0,0,0],[0,0]],[[-2916,10692,5724],[10692,17280,1728],[5724,1728]],[[0,0,0],[0,0,0],[0,0]],[[36936,172044,25092],[172044,81288,1584],[25092,1584]],[[0,0,0],[0,0,0],[0,0]],[[1041012,991116,51480],[991116,172944,576],[51480,576]],[[0,0,0],[0,0,0],[0,0]],[[8022456,3050856,59184],[3050856,204768,72],[59184,72]],[[0,0,0],[0,0],[0]],[[33380604,5842188,40896],[5842188,145584],[40896]],[[0,0,0],[0,0],[0]],[[89506800,7499772,17316],[7499772,63432],[17316]],[[0,0,0],[0,0],[0]],[[167964840,6716880,4392],[6716880,16560],[4392]],[[0,0,0],[0,0],[0]],[[231027048,4281516,612],[4281516,2376],[612]],[[0,0,0],[0,0],[0]],[[239478120,1953252,36],[1953252,144],[36]],[[0,0],[0]],[[190218960,632736],[632736]],[[0,0],[0]],[[116803080,142020],[142020]],[[0,0],[0]],[[55581768,20988],[20988]],[[0,0],[0]],[[20422764,1836],[1836]],[[0,0],[0]],[[5733936,72],[72]],[[0]],[[1206360]],[[0]],[[183960]],[[0]],[[19188]],[[0]],[[1224]],[[0]],[[36]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
