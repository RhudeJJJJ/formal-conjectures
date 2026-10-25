/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode033
import Proofs.RadenkovicGutmanD44Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1936]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,46464],[0,46464,88]],[[0,0,0],[0,0,0],[0,0]],[[-156816,-104544,261360],[-104544,1010592,144848],[261360,144848]],[[0,0,0],[0,0,0],[0,0]],[[-4293432,3972672,1575288],[3972672,5999136,151360],[1575288,151360]],[[0,0,0],[0,0,0],[0,0]],[[-18366480,38879280,3940992],[38879280,14737888,61952],[3940992,61952]],[[0,0,0],[0,0,0],[0,0]],[[44552904,155120416,5339840],[155120416,19585984,9152],[5339840,9152]],[[0,0,0],[0,0,0],[0,0]],[[633994064,356316576,4283488],[356316576,15414784,176],[4283488,176]],[[0,0,0],[0,0],[0]],[[2622504456,531310912,2087536],[531310912,7382144],[2087536]],[[0,0,0],[0,0],[0]],[[6455663456,543978512,608256],[543978512,2119392],[608256]],[[0,0,0],[0,0],[0]],[[10911718224,392885152,98560],[392885152,340032],[98560]],[[0,0,0],[0,0],[0]],[[13438636288,202033568,7216],[202033568,24992],[7216]],[[0,0,0],[0,0],[0]],[[12428267808,73591584,88],[73591584,352],[88]],[[0,0],[0]],[[8766578656,18591760],[18591760]],[[0,0],[0]],[[4746614400,3115200],[3115200]],[[0,0],[0]],[[1970937936,316448],[316448]],[[0,0],[0]],[[622537608,15840],[15840]],[[0,0],[0]],[[147076512,176],[176]],[[0]],[[25238224]],[[0]],[[2991472]],[[0]],[[223432]],[[0]],[[8624]],[[0]],[[88]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
