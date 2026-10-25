/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode033
import Proofs.RadenkovicGutmanD41Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1681]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,30258],[0,30258]],[[0,0,0],[0,0,0],[0,0]],[[-136161,0,136161],[0,544644,80688],[136161,80688]],[[0,0,0],[0,0,0],[0,0]],[[-2360124,2450898,726192],[2450898,2904768,73964],[726192,73964]],[[0,0,0],[0,0,0],[0,0]],[[-7216533,19607184,1633932],[19607184,6535728,26896],[1633932,26896]],[[0,0,0],[0,0,0],[0,0]],[[34292400,70259076,2017200],[70259076,8068800,3362],[2017200,3362]],[[0,0,0],[0,0],[0]],[[326825063,148869360,1489366],[148869360,5957464],[1489366]],[[0,0,0],[0,0],[0]],[[1206460424,207418590,672400],[207418590,2689600],[672400]],[[0,0,0],[0,0],[0]],[[2756123894,199944864,181548],[199944864,726192],[181548]],[[0,0,0],[0,0],[0]],[[4389111172,136618232,26896],[136618232,107584],[26896]],[[0,0,0],[0,0],[0]],[[5134130372,66648288,1681],[66648288,6724],[1681]],[[0,0],[0]],[[4532197892,23046510],[23046510]],[[0,0],[0]],[[3061356512,5513680],[5513680]],[[0,0],[0]],[[1590427720,867396],[867396]],[[0,0],[0]],[[634192551,80688],[80688]],[[0,0],[0]],[[192279504,3362],[3362]],[[0]],[[43500918]],[[0]],[[7107268]],[[0]],[[791751]],[[0]],[[53792]],[[0]],[[1681]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
