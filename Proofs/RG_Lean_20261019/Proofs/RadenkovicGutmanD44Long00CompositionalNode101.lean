/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode051
import Proofs.RadenkovicGutmanD44Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1936]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,46464],[0,46464,88]],[[0,0,0],[0,0,0],[0,0]],[[-156816,104544,261360],[104544,1047024,144848],[261360,144848]],[[0,0,0],[0,0,0],[0,0]],[[-829224,7018704,1575288],[7018704,6314880,151360],[1575288,151360]],[[0,0,0],[0,0,0],[0,0]],[[38358144,57719376,3940992],[57719376,15810608,61952],[3940992,61952]],[[0,0,0],[0,0,0],[0,0]],[[457653768,220624976,5339840],[220624976,21439968,9152],[5339840,9152]],[[0,0,0],[0,0,0],[0,0]],[[2412805472,499540800,4283488],[499540800,17212096,176],[4283488,176]],[[0,0,0],[0,0],[0]],[[7705507128,740368112,2087536],[740368112,8394144],[2087536]],[[0,0,0],[0,0],[0]],[[16713032512,754849744,608256],[754849744,2447280],[608256]],[[0,0,0],[0,0],[0]],[[26093132560,542640384,98560],[542640384,396704],[98560]],[[0,0,0],[0,0],[0]],[[30320457904,277368608,7216],[277368608,29040],[7216]],[[0,0,0],[0,0],[0]],[[26747363456,100257168,88],[100257168,352],[88]],[[0,0],[0]],[[18108312640,25080880],[25080880]],[[0,0],[0]],[[9446166400,4148144],[4148144]],[[0,0],[0]],[[3788047296,413248],[413248]],[[0,0],[0]],[[1157167352,19888],[19888]],[[0,0],[0]],[[264515328,176],[176]],[[0]],[[43875920]],[[0]],[[5008960]],[[0]],[[356664]],[[0]],[[12672]],[[0]],[[88]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
