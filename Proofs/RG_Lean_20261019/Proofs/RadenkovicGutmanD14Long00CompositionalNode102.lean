/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode100
import Proofs.RadenkovicGutmanD14Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,196]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-1764],[0,-3528,5712],[-1764,5712,28]],[[0,0,0],[0,0,0],[0,0]],[[-15876,-59724,20244],[-59724,109032,19376],[20244,19376]],[[0,0,0],[0,0,0],[0,0]],[[-740124,123228,172592],[123228,772408,21616],[172592,21616]],[[0,0,0],[0,0,0],[0,0]],[[-4128516,3980844,492856],[3980844,2076760,9464],[492856,9464]],[[0,0,0],[0,0,0],[0,0]],[[3105564,19974080,726488],[19974080,2951760,1568],[726488,1568]],[[0,0,0],[0,0,0],[0,0]],[[108477572,51759764,621264],[51759764,2458736,56],[621264,56]],[[0,0,0],[0,0],[0]],[[506685676,83748700,319564],[83748700,1240008],[319564]],[[0,0,0],[0,0],[0]],[[1331498840,91185416,98056],[91185416,375032],[98056]],[[0,0,0],[0,0],[0]],[[2351383552,69167532,16884],[69167532,64008],[16884]],[[0,0,0],[0,0],[0]],[[2988449520,37049796,1372],[37049796,5208],[1372]],[[0,0,0],[0,0],[0]],[[2828578144,13985664,28],[13985664,112],[28]],[[0,0],[0]],[[2030126280,3653300],[3653300]],[[0,0],[0]],[[1113854840,633892],[633892]],[[0,0],[0]],[[467377092,67284],[67284]],[[0,0],[0]],[[148937516,3640],[3640]],[[0,0],[0]],[[35481768,56],[56]],[[0]],[[6144880]],[[0]],[[737324]],[[0]],[[56196]],[[0]],[[2268]],[[0]],[[28]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
