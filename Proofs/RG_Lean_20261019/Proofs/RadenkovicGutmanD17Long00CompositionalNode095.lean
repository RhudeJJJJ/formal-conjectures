/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode093
import Proofs.RadenkovicGutmanD17Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,289]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-2601],[0,-5202,8466],[-2601,8466,34]],[[0,0,0],[0,0,0],[0,0]],[[-23409,-87669,30243],[-87669,160854,28628],[30243,28628]],[[0,0,0],[0,0,0],[0,0]],[[-1097010,184059,256649],[184059,1134682,31756],[256649,31756]],[[0,0,0],[0,0,0],[0,0]],[[-6254793,5838633,731170],[5838633,3036234,13736],[731170,13736]],[[0,0,0],[0,0,0],[0,0]],[[2693616,29149832,1075148],[29149832,4292500,2210],[1075148,2210]],[[0,0,0],[0,0,0],[0,0]],[[148639517,75201149,916572],[75201149,3554156,68],[916572,68]],[[0,0,0],[0,0],[0]],[[705081936,121142595,469387],[121142595,1779866],[469387]],[[0,0,0],[0,0],[0]],[[1857968998,131311264,143038],[131311264,533426],[143038]],[[0,0,0],[0,0],[0]],[[3279515730,99144085,24327],[99144085,89794],[24327]],[[0,0,0],[0,0],[0]],[[4160921904,52845435,1921],[52845435,7106],[1921]],[[0,0,0],[0,0],[0]],[[3929422704,19839238,34],[19839238,136],[34]],[[0,0],[0]],[[2813009346,5148875],[5148875]],[[0,0],[0]],[[1539114142,885887],[885887]],[[0,0],[0]],[[643878757,92837],[92837]],[[0,0],[0]],[[204500616,4896],[4896]],[[0,0],[0]],[[48531498,68],[68]],[[0]],[[8365054]],[[0]],[[997271]],[[0]],[[75242]],[[0]],[[2975]],[[0]],[[34]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
