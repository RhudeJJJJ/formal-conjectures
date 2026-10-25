/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode090
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e091 : NestedArithmetic.Expr 3 := .scaled (-1) e090
noncomputable def p091 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2523],[0,2523]],[[0,0,0],[0,0,0],[0,0]],[[0,22707,37845],[22707,121104,11107],[37845,11107]],[[0,0,0],[0,0,0],[0,0]],[[408726,1409400,291711],[1409400,904452,14210],[291711,14210]],[[0,0,0],[0,0,0],[0,0]],[[14197356,13217562,895694],[13217562,2691316,6815],[895694,6815]],[[0,0,0],[0,0,0],[0,0]],[[146655900,57161668,1437269],[57161668,4208364,1247],[1437269,1247]],[[0,0,0],[0,0,0],[0,0]],[[784307088,144300578,1325590],[144300578,3808744,58],[1325590,58]],[[0,0,0],[0,0],[0]],[[2616076254,235239242,725667],[235239242,2061668],[725667]],[[0,0,0],[0,0],[0]],[[5960261540,260819388,233798],[260819388,662708],[233798]],[[0,0,0],[0,0],[0]],[[9768935360,202025049,41615],[202025049,119364],[41615]],[[0,0,0],[0,0],[0]],[[11889526314,110479821,3393],[110479821,10208],[3393]],[[0,0,0],[0,0],[0]],[[10957376762,42517973,58],[42517973,232],[58]],[[0,0],[0]],[[7732545442,11301764],[11301764]],[[0,0],[0]],[[4197435408,1990879],[1990879]],[[0,0],[0]],[[1749924148,213846],[213846]],[[0,0],[0]],[[555789002,11629],[11629]],[[0,0],[0]],[[132303800,174],[174]],[[0]],[[22950368]],[[0]],[[2766194]],[[0]],[[212744]],[[0]],[[8758]],[[0]],[[116]]]
theorem step091 : p091=NestedHorner.scale (-1) p090 := by decide +kernel
#print axioms step091
theorem h091 : NestedArithmetic.compile e091=p091 := StagedExprCompile.compile_scaled (-1) e091 e090 p090 p091 rfl h090 step091
#print axioms h091
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
