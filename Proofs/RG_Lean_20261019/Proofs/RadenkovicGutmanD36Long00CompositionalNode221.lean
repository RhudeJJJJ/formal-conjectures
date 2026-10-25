/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode220
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e221 : NestedArithmetic.Expr 3 := .scaled (-1) e220
noncomputable def p221 : NestedHorner.Poly 3 := [[[2592],[0],[0]],[[0,0],[0,0],[0]],[[80352,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1143072,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[9891072,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[58180032,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[246276288,3888,0],[3888,0],[0]],[[0,0,0],[0,0],[0]],[[774772128,86832,0],[86832,0],[0]],[[0,0,0],[0,0],[0]],[[1844697888,861840,0],[861840,0],[0]],[[0,0,0],[0,0],[0]],[[3353695488,5010336,0],[5010336,0],[0]],[[0,0,0],[0,0],[0]],[[4662953568,18933264,0],[18933264,0],[0]],[[0,0,0],[0,0],[0]],[[4933102176,48806064,1296],[48806064,2592],[1296]],[[0,0,0],[0,0],[0]],[[3921846336,87656256,18144],[87656256,36288],[18144]],[[0,0,0],[0,0],[0]],[[2292100416,110078352,104976],[110078352,209952],[104976]],[[0,0,0],[0,0],[0]],[[949729536,95545008,324000],[95545008,648000],[324000]],[[0,0,0],[0,0],[0]],[[262370016,55663200,575424],[55663200,1150848],[575424]],[[0,0,0],[0,0],[0]],[[43040160,20563632,593568],[20563632,1187136],[593568]],[[0,0,0],[0,0],[0]],[[3149280,4304016,343440],[4304016,686880],[343440]],[[0,0,0],[0,0],[0]],[[0,384912,101088],[384912,202176],[101088]],[[0,0,0],[0,0],[0]],[[0,0,11664],[0,23328],[11664]]]
theorem step221 : p221=NestedHorner.scale (-1) p220 := by decide +kernel
#print axioms step221
theorem h221 : NestedArithmetic.compile e221=p221 := StagedExprCompile.compile_scaled (-1) e221 e220 p220 p221 rfl h220 step221
#print axioms h221
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
