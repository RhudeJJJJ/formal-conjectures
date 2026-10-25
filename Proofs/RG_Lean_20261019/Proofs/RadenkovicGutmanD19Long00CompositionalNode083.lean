/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode070
import Proofs.RadenkovicGutmanD19Long00CompositionalNode082
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e083 : NestedArithmetic.Expr 3 := .plus e070 e082
noncomputable def p083 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,456],[0,456,1232]],[[0,0,0],[0,0,0],[0,0,0]],[[0,4104,17100],[4104,39960,24608],[17100,24608,4]],[[0,0,0],[0,0,0],[0,0]],[[-47952,575100,245256],[575100,733932,63616],[245256,63616]],[[0,0,0],[0,0,0],[0,0]],[[3089232,7868736,1023280],[7868736,3250416,57896],[1023280,57896]],[[0,0,0],[0,0,0],[0,0]],[[54894132,42794972,2054992],[42794972,6754668,21104],[2054992,21104]],[[0,0,0],[0,0,0],[0,0]],[[380516964,127982428,2335160],[127982428,7906456,2680],[2335160,2680]],[[0,0,0],[0,0,0],[0,0]],[[1508260700,240942692,1602512],[240942692,5589856,8],[1602512,8]],[[0,0,0],[0,0],[0]],[[3932400720,305936936,676084],[305936936,2431376],[676084]],[[0,0,0],[0,0],[0]],[[7245926136,271996704,171440],[271996704,636012],[171440]],[[0,0,0],[0,0],[0]],[[9840195296,172531476,24020],[172531476,91968],[24020]],[[0,0,0],[0,0],[0]],[[10105892236,78475700,1448],[78475700,5724],[1448]],[[0,0,0],[0,0],[0]],[[7971899832,25391076,4],[25391076,16],[4]],[[0,0],[0]],[[4869997072,5704188],[5704188]],[[0,0],[0]],[[2308838520,846424],[846424]],[[0,0],[0]],[[846282420,74860],[74860]],[[0,0],[0]],[[237327840,3044],[3044]],[[0,0],[0]],[[49947784,8],[8]],[[0]],[[7635072]],[[0]],[[801204]],[[0]],[[51848]],[[0]],[[1596]],[[0]],[[4]]]
theorem step083 : p083=NestedHorner.add p070 p082 := by decide +kernel
#print axioms step083
theorem h083 : NestedArithmetic.compile e083=p083 := StagedExprCompile.compile_plus e083 e070 e082 p070 p082 p083 rfl h070 h082 step083
#print axioms h083
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
