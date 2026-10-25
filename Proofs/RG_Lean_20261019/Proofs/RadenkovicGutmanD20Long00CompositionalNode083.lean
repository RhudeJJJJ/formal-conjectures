/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode070
import Proofs.RadenkovicGutmanD20Long00CompositionalNode082
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e083 : NestedArithmetic.Expr 3 := .plus e070 e082
noncomputable def p083 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,480],[0,480,1376]],[[0,0,0],[0,0,0],[0,0,0]],[[0,4320,18720],[4320,43488,27328],[18720,27328,4]],[[0,0,0],[0,0,0],[0,0]],[[-57024,628992,270816],[628992,810552,70760],[270816,70760]],[[0,0,0],[0,0,0],[0,0]],[[3331476,8662392,1132516],[8662392,3600128,64416],[1132516,64416]],[[0,0,0],[0,0,0],[0,0]],[[60064200,47231800,2276640],[47231800,7489976,23472],[2276640,23472]],[[0,0,0],[0,0,0],[0,0]],[[418155564,141437832,2588368],[141437832,8771824,2976],[2588368,2976]],[[0,0,0],[0,0,0],[0,0]],[[1660952920,266481856,1776736],[266481856,6202976,8],[1776736,8]],[[0,0,0],[0,0],[0]],[[4335932804,338531048,749624],[338531048,2697968],[749624]],[[0,0,0],[0,0],[0]],[[7996048432,301067576,190048],[301067576,705528],[190048]],[[0,0,0],[0,0],[0]],[[10865079256,191004976,26608],[191004976,101936],[26608]],[[0,0,0],[0,0],[0]],[[11162989464,86883488,1600],[86883488,6328],[1600]],[[0,0,0],[0,0],[0]],[[8808328288,28109640,4],[28109640,16],[4]],[[0,0],[0]],[[5382029600,6313480],[6313480]],[[0,0],[0]],[[2551888032,936360],[936360]],[[0,0],[0]],[[935404744,82720],[82720]],[[0,0],[0]],[[262307300,3352],[3352]],[[0,0],[0]],[[55195664,8],[8]],[[0]],[[8434360]],[[0]],[[884488]],[[0]],[[57156]],[[0]],[[1752]],[[0]],[[4]]]
theorem step083 : p083=NestedHorner.add p070 p082 := by decide +kernel
#print axioms step083
theorem h083 : NestedArithmetic.compile e083=p083 := StagedExprCompile.compile_plus e083 e070 e082 p070 p082 p083 rfl h070 h082 step083
#print axioms h083
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
