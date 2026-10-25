/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode075
import Proofs.RadenkovicGutmanD43Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1849]],[[0,0],[0,0,0],[0,0]],[[0,0,16641],[0,33282,33282],[16641,33282]],[[0,0,0],[0,0,0],[0,0]],[[-149769,549153,293991],[549153,887520,88752],[293991,88752]],[[0,0,0],[0,0,0],[0,0]],[[1897074,8836371,1288753],[8836371,4175042,81356],[1288753,81356]],[[0,0,0],[0,0,0],[0,0]],[[53467533,50904819,2644070],[50904819,8882596,29584],[2644070,29584]],[[0,0,0],[0,0,0],[0,0]],[[412042254,156695354,3039756],[156695354,10517112,3698],[3039756,3698]],[[0,0,0],[0,0],[0]],[[1714464911,300061267,2100464],[300061267,7477356],[2100464]],[[0,0,0],[0,0],[0]],[[4597168700,385196623,889369],[385196623,3257938],[889369]],[[0,0,0],[0,0],[0]],[[8626860810,344986420,225578],[344986420,850540],[225578]],[[0,0,0],[0,0],[0]],[[11865805882,219903419,31433],[219903419,122034],[31433]],[[0,0,0],[0,0],[0]],[[12299862330,100321193,1849],[100321193,7396],[1849]],[[0,0],[0]],[[9769857140,32498024],[32498024]],[[0,0],[0]],[[5999135970,7294305],[7294305]],[[0,0],[0]],[[2854741362,1077967],[1077967]],[[0,0],[0]],[[1048935851,94299],[94299]],[[0,0],[0]],[[294501324,3698],[3698]],[[0]],[[61959990]],[[0]],[[9448390]],[[0]],[[985517]],[[0]],[[62866]],[[0]],[[1849]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
