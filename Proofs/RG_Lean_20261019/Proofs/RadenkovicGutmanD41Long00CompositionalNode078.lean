/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode075
import Proofs.RadenkovicGutmanD41Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1681]],[[0,0],[0,0,0],[0,0]],[[0,0,15129],[0,30258,30258],[15129,30258]],[[0,0,0],[0,0,0],[0,0]],[[-136161,499257,267279],[499257,806880,80688],[267279,80688]],[[0,0,0],[0,0,0],[0,0]],[[1724706,8033499,1171657],[8033499,3795698,73964],[1171657,73964]],[[0,0,0],[0,0,0],[0,0]],[[48609477,46279611,2403830],[46279611,8075524,26896],[2403830,26896]],[[0,0,0],[0,0,0],[0,0]],[[374604126,142458026,2763564],[142458026,9561528,3362],[2763564,3362]],[[0,0,0],[0,0],[0]],[[1558688759,272797723,1909616],[272797723,6797964],[1909616]],[[0,0,0],[0,0],[0]],[[4179470300,350197687,808561],[350197687,2961922],[808561]],[[0,0,0],[0,0],[0]],[[7843024890,313640980,205082],[313640980,773260],[205082]],[[0,0,0],[0,0],[0]],[[10787679658,199923011,28577],[199923011,110946],[28577]],[[0,0,0],[0,0],[0]],[[11182297770,91206017,1681],[91206017,6724],[1681]],[[0,0],[0]],[[8882168660,29545256],[29545256]],[[0,0],[0]],[[5454054930,6631545],[6631545]],[[0,0],[0]],[[2595359778,980023],[980023]],[[0,0],[0]],[[953629619,85731],[85731]],[[0,0],[0]],[[267742956,3362],[3362]],[[0]],[[56330310]],[[0]],[[8589910]],[[0]],[[895973]],[[0]],[[57154]],[[0]],[[1681]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
