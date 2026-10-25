/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode076
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e077 : NestedArithmetic.Expr 3 := .scaled (-1) e076
noncomputable def p077 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,11664],[0,23328],[11664]],[[0,0,0],[0,0],[0]],[[0,384912,101088],[384912,202176],[101088]],[[0,0,0],[0,0],[0]],[[3149280,4304016,343440],[4304016,686880],[343440]],[[0,0,0],[0,0],[0]],[[43040160,20563632,593568],[20563632,1187136],[593568]],[[0,0,0],[0,0],[0]],[[262370016,55663200,575424],[55663200,1150848],[575424]],[[0,0,0],[0,0],[0]],[[949729536,95545008,324000],[95545008,648000],[324000]],[[0,0,0],[0,0],[0]],[[2292100416,110078352,104976],[110078352,209952],[104976]],[[0,0,0],[0,0],[0]],[[3921846336,87656256,18144],[87656256,36288],[18144]],[[0,0,0],[0,0],[0]],[[4933102176,48806064,1296],[48806064,2592],[1296]],[[0,0],[0]],[[4662953568,18933264],[18933264]],[[0,0],[0]],[[3353695488,5010336],[5010336]],[[0,0],[0]],[[1844697888,861840],[861840]],[[0,0],[0]],[[774772128,86832],[86832]],[[0,0],[0]],[[246276288,3888],[3888]],[[0]],[[58180032]],[[0]],[[9891072]],[[0]],[[1143072]],[[0]],[[80352]],[[0]],[[2592]]]
theorem step077 : p077=NestedHorner.scale (-1) p076 := by decide +kernel
#print axioms step077
theorem h077 : NestedArithmetic.compile e077=p077 := StagedExprCompile.compile_scaled (-1) e077 e076 p076 p077 rfl h076 step077
#print axioms h077
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
