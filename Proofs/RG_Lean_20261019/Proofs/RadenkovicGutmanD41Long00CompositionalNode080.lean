/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode035
import Proofs.RadenkovicGutmanD41Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-5043],[0,-5043]],[[0,0,0],[0,0,0],[0,0]],[[0,-45387,-45387],[-45387,-181548,-21853],[-45387,-21853]],[[0,0,0],[0,0,0],[0,0]],[[-816966,-1815480,-317709],[-1815480,-1270836,-26896],[-317709,-26896]],[[0,0,0],[0,0,0],[0,0]],[[-20151828,-15129000,-877482],[-15129000,-3509928,-11767],[-877482,-11767]],[[0,0,0],[0,0,0],[0,0]],[[-180095616,-59867134,-1272517],[-59867134,-5090068,-1681],[-1272517,-1681]],[[0,0,0],[0,0],[0]],[[-874637748,-139902906,-1069116],[-139902906,-4276464],[-1069116]],[[0,0,0],[0,0],[0]],[[-2704994598,-212693568,-536239],[-212693568,-2144956],[-536239]],[[0,0,0],[0,0],[0]],[[-5780864864,-221101930,-158014],[-221101930,-632056],[-158014]],[[0,0,0],[0,0],[0]],[[-8953772536,-161169237,-25215],[-161169237,-100860],[-25215]],[[0,0,0],[0,0],[0]],[[-10350276734,-83103597,-1681],[-83103597,-6724],[-1681]],[[0,0],[0]],[[-9091577554,-30138649],[-30138649]],[[0,0],[0]],[[-6128949534,-7514070],[-7514070]],[[0,0],[0]],[[-3181796800,-1225449],[-1225449]],[[0,0],[0]],[[-1268469152,-117670],[-117670]],[[0,0],[0]],[[-384562370,-5043],[-5043]],[[0]],[[-87001836]],[[0]],[[-14214536]],[[0]],[[-1583502]],[[0]],[[-107584]],[[0]],[[-3362]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
