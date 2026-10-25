/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode089
import Proofs.RadenkovicGutmanD38Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,8664],[0,8664,-2736]],[[0,0,0],[0,0,0],[0,0]],[[0,0,103968],[0,350892,-11476],[103968,-11476]],[[0,0,0],[0,0,0],[0,0]],[[338580,2848176,551532],[2848176,1642968,-84132],[551532,-84132]],[[0,0,0],[0,0,0],[0,0]],[[24502932,24710184,1105268],[24710184,2507772,-98952],[1105268,-98952]],[[0,0,0],[0,0,0],[0,0]],[[265298976,93311964,889200],[93311964,250040,-40356],[889200,-40356]],[[0,0,0],[0,0,0],[0,0]],[[1383711708,200141288,-106628],[200141288,-3632192,-5396],[-106628,-5396]],[[0,0,0],[0,0],[0]],[[4401056716,265793356,-732488],[265793356,-4734952],[-732488]],[[0,0,0],[0,0],[0]],[[9432407728,220189480,-564756],[220189480,-2843844],[-564756]],[[0,0,0],[0,0],[0]],[[14336701712,102282928,-204592],[102282928,-919448],[-204592]],[[0,0,0],[0,0],[0]],[[15865892468,9124788,-36860],[9124788,-154660],[-36860]],[[0,0,0],[0,0],[0]],[[12900386832,-20394448,-2660],[-20394448,-10640],[-2660]],[[0,0],[0]],[[7638626848,-14412868],[-14412868]],[[0,0],[0]],[[3165651864,-4979596],[-4979596]],[[0,0],[0]],[[802987652,-995372],[-995372]],[[0,0],[0]],[[41479052,-110124],[-110124]],[[0,0],[0]],[[-58772320,-5244],[-5244]],[[0]],[[-27106768]],[[0]],[[-6380884]],[[0]],[[-900828]],[[0]],[[-72580]],[[0]],[[-2584]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
