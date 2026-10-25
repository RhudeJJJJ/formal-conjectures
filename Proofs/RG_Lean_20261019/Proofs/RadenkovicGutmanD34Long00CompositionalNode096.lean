/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode043
import Proofs.RadenkovicGutmanD34Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3468],[0,3468,-2176]],[[0,0,0],[0,0,0],[0,0]],[[0,31212,31212],[31212,127296,-24140],[31212,-24140]],[[0,0,0],[0,0,0],[0,0]],[[760104,1270512,42228],[1270512,190128,-85952],[42228,-85952]],[[0,0,0],[0,0,0],[0,0]],[[17493408,7481088,-336600],[7481088,-1274320,-87652],[-336600,-87652]],[[0,0,0],[0,0,0],[0,0]],[[138919104,17000680,-1239980],[17000680,-4835344,-33660],[-1239980,-33660]],[[0,0,0],[0,0,0],[0,0]],[[587955744,8598600,-1875984],[8598600,-7383168,-4352],[-1875984,-4352]],[[0,0,0],[0,0],[0]],[[1542619848,-40605520,-1559172],[-40605520,-6168688],[-1559172]],[[0,0,0],[0,0],[0]],[[2661073376,-109599000,-761736],[-109599000,-3024912],[-761736]],[[0,0,0],[0,0],[0]],[[3006777760,-142432460,-217668],[-142432460,-866864],[-217668]],[[0,0,0],[0,0],[0]],[[1956998248,-116548940,-33660],[-116548940,-134368],[-33660]],[[0,0,0],[0,0],[0]],[[96749992,-64304812,-2176],[-64304812,-8704],[-2176]],[[0,0],[0]],[[-1299725480,-24331080],[-24331080]],[[0,0],[0]],[[-1581112064,-6236076],[-6236076]],[[0,0],[0]],[[-1105139536,-1035912],[-1035912]],[[0,0],[0]],[[-530639496,-100708],[-100708]],[[0,0],[0]],[[-182964336,-4352],[-4352]],[[0]],[[-45497440]],[[0]],[[-7991224]],[[0]],[[-942480]],[[0]],[[-67048]],[[0]],[[-2176]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
