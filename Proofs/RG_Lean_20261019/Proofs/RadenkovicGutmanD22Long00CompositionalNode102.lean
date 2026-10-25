/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode100
import Proofs.RadenkovicGutmanD22Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,484]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-4356],[0,-8712,14256],[-4356,14256,44]],[[0,0,0],[0,0,0],[0,0]],[[-39204,-146124,51348],[-146124,273768,48048],[51348,48048]],[[0,0,0],[0,0,0],[0,0]],[[-1809324,350460,433664],[350460,1929400,52976],[433664,52976]],[[0,0,0],[0,0,0],[0,0]],[[-9771300,10153836,1232440],[10153836,5163224,22616],[1232440,22616]],[[0,0,0],[0,0,0],[0,0]],[[11046156,50373312,1807608],[50373312,7297488,3520],[1807608,3520]],[[0,0,0],[0,0,0],[0,0]],[[282110180,129715124,1535952],[129715124,6034160,88],[1535952,88]],[[0,0,0],[0,0],[0]],[[1288225180,208786556,782892],[208786556,3011976],[782892]],[[0,0,0],[0,0],[0]],[[3351404056,226151464,236808],[226151464,896632],[236808]],[[0,0,0],[0,0],[0]],[[5878874144,170577836,39732],[170577836,148808],[39732]],[[0,0,0],[0,0],[0]],[[7431039792,90768260,3036],[90768260,11352],[3036]],[[0,0,0],[0,0],[0]],[[6998645984,33981024,44],[33981024,176],[44]],[[0,0],[0]],[[4998473480,8777780],[8777780]],[[0,0],[0]],[[2728334136,1497892],[1497892]],[[0,0],[0]],[[1138228388,154484],[154484]],[[0,0],[0]],[[360246876,7832],[7832]],[[0,0],[0]],[[85087464,88],[88]],[[0]],[[14564880]],[[0]],[[1717452]],[[0]],[[127028]],[[0]],[[4796]],[[0]],[[44]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
