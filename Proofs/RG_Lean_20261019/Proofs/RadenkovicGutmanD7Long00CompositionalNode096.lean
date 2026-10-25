/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode043
import Proofs.RadenkovicGutmanD7Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,147],[0,147,-70]],[[0,0,0],[0,0,0],[0,0]],[[0,1323,1323],[1323,5796,-623],[1323,-623]],[[0,0,0],[0,0,0],[0,0]],[[34020,57456,3591],[57456,18732,-2576],[3591,-2576]],[[0,0,0],[0,0,0],[0,0]],[[805140,390348,-4662],[390348,-3808,-2737],[-4662,-2737]],[[0,0,0],[0,0,0],[0,0]],[[6729534,1178086,-30947],[1178086,-98140,-1071],[-30947,-1071]],[[0,0,0],[0,0,0],[0,0]],[[30422700,1839474,-52836],[1839474,-186480,-140],[-52836,-140]],[[0,0,0],[0,0],[0]],[[86959236,1201928,-46389],[1201928,-171556],[-46389]],[[0,0,0],[0,0],[0]],[[169199744,-782250,-23394],[-782250,-89040],[-23394]],[[0,0,0],[0,0],[0]],[[232101268,-2484251,-6825],[-2484251,-26516],[-6825]],[[0,0,0],[0,0],[0]],[[226160494,-2618147,-1071],[-2618147,-4228],[-1071]],[[0,0,0],[0,0],[0]],[[152217226,-1640863,-70],[-1640863,-280],[-70]],[[0,0],[0]],[[62450710,-671790],[-671790]],[[0,0],[0]],[[5133184,-181839],[-181839]],[[0,0],[0]],[[-12513256,-31458],[-31458]],[[0,0],[0]],[[-9878400,-3157],[-3157]],[[0,0],[0]],[[-4213860,-140],[-140]],[[0]],[[-1183420]],[[0]],[[-225106]],[[0]],[[-28098]],[[0]],[[-2086]],[[0]],[[-70]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
