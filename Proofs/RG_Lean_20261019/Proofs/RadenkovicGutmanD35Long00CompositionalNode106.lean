/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode095
import Proofs.RadenkovicGutmanD35Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2520,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-22680,-22680,0],[-22680,-21840,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-597240,-257040,0],[-257040,-74200,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5896800,-1247400,0],[-1247400,-128240,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-31778040,-3435600,0],[-3435600,-124320,0],[0,0]],[[0,0,0],[0,0],[0]],[[-108600520,-6006280,0],[-6006280,-70000],[0]],[[0,0,0],[0,0],[0]],[[-254653840,-7050400,0],[-7050400,-22680],[0]],[[0,0,0],[0,0],[0]],[[-429375520,-5719280,0],[-5719280,-3920],[0]],[[0,0,0],[0,0],[0]],[[-536139240,-3242400,0],[-3242400,-280],[0]],[[0,0,0],[0,0],[0]],[[-504994000,-1279880,0],[-1279880,0],[0]],[[0,0],[0]],[[-362626320,-344400],[-344400]],[[0,0],[0]],[[-199333120,-60200],[-60200]],[[0,0],[0]],[[-83700680,-6160],[-6160]],[[0,0],[0]],[[-26604200,-280],[-280]],[[0,0],[0]],[[-6284880,0],[0]],[[0]],[[-1068480]],[[0]],[[-123480]],[[0]],[[-8680]],[[0]],[[-280]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
