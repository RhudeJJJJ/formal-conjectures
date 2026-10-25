/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode051
import Proofs.RadenkovicGutmanD19Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,361]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,8664],[0,8664,38]],[[0,0,0],[0,0,0],[0,0]],[[-29241,19494,48735],[19494,195624,27398],[48735,27398]],[[0,0,0],[0,0,0],[0,0]],[[-152874,1312254,295488],[1312254,1187880,29260],[295488,29260]],[[0,0,0],[0,0,0],[0,0]],[[7214319,10833876,744192],[10833876,2996908,12502],[744192,12502]],[[0,0,0],[0,0,0],[0,0]],[[86154018,41583476,1016690],[41583476,4101568,2052],[1016690,2052]],[[0,0,0],[0,0,0],[0,0]],[[455249747,94580100,824638],[94580100,3332296,76],[824638,76]],[[0,0,0],[0,0],[0]],[[1457768578,140892562,408386],[140892562,1652544],[408386]],[[0,0,0],[0,0],[0]],[[3171196862,144505944,122056],[144505944,494380],[122056]],[[0,0,0],[0,0],[0]],[[4967125160,104634634,20710],[104634634,83904],[20710]],[[0,0,0],[0,0],[0]],[[5792821004,53974858,1691],[53974858,6840],[1691]],[[0,0,0],[0,0],[0]],[[5131322856,19748068,38],[19748068,152],[38]],[[0,0],[0]],[[3490738140,5025880],[5025880]],[[0,0],[0]],[[1831459400,853594],[853594]],[[0,0],[0]],[[739681571,89148],[89148]],[[0,0],[0]],[[228022002,4788],[4788]],[[0,0],[0]],[[52762278,76],[76]],[[0]],[[8904920]],[[0]],[[1044335]],[[0]],[[78014]],[[0]],[[3097]],[[0]],[[38]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
