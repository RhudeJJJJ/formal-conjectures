/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode095
import Proofs.RadenkovicGutmanD28Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2016,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-18144,-18144,0],[-18144,-17472,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-477792,-205632,0],[-205632,-59360,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4717440,-997920,0],[-997920,-102592,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-25422432,-2748480,0],[-2748480,-99456,0],[0,0]],[[0,0,0],[0,0],[0]],[[-86880416,-4805024,0],[-4805024,-56000],[0]],[[0,0,0],[0,0],[0]],[[-203723072,-5640320,0],[-5640320,-18144],[0]],[[0,0,0],[0,0],[0]],[[-343500416,-4575424,0],[-4575424,-3136],[0]],[[0,0,0],[0,0],[0]],[[-428911392,-2593920,0],[-2593920,-224],[0]],[[0,0,0],[0,0],[0]],[[-403995200,-1023904,0],[-1023904,0],[0]],[[0,0],[0]],[[-290101056,-275520],[-275520]],[[0,0],[0]],[[-159466496,-48160],[-48160]],[[0,0],[0]],[[-66960544,-4928],[-4928]],[[0,0],[0]],[[-21283360,-224],[-224]],[[0,0],[0]],[[-5027904,0],[0]],[[0]],[[-854784]],[[0]],[[-98784]],[[0]],[[-6944]],[[0]],[[-224]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
