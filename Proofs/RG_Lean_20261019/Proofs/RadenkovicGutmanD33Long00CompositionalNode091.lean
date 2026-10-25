/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode090
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e091 : NestedArithmetic.Expr 3 := .scaled (-1) e090
noncomputable def p091 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3267],[0,3267]],[[0,0,0],[0,0,0],[0,0]],[[0,29403,49005],[29403,156816,14355],[49005,14355]],[[0,0,0],[0,0,0],[0,0]],[[529254,1824768,377487],[1824768,1170180,18282],[377487,18282]],[[0,0,0],[0,0,0],[0,0]],[[18379548,17105418,1158102],[17105418,3478068,8679],[1158102,8679]],[[0,0,0],[0,0,0],[0,0]],[[189793692,73935972,1856349],[73935972,5430348,1551],[1856349,1551]],[[0,0,0],[0,0,0],[0,0]],[[1014613776,186528738,1709598],[186528738,4904328,66],[1709598,66]],[[0,0,0],[0,0],[0]],[[3382786638,303850602,933867],[303850602,2646468],[933867]],[[0,0,0],[0,0],[0]],[[7703216532,336579804,299838],[336579804,846516],[299838]],[[0,0,0],[0,0],[0]],[[12618361536,260402241,53031],[260402241,151140],[53031]],[[0,0,0],[0,0],[0]],[[15347104410,142186077,4257],[142186077,12672],[4257]],[[0,0,0],[0,0],[0]],[[14132513274,54605925,66],[54605925,264],[66]],[[0,0],[0]],[[9963537474,14471292],[14471292]],[[0,0],[0]],[[5402013408,2537271],[2537271]],[[0,0],[0]],[[2248723092,270270],[270270]],[[0,0],[0]],[[712814586,14421],[14421]],[[0,0],[0]],[[169235880,198],[198]],[[0]],[[29246976]],[[0]],[[3504930]],[[0]],[[266904]],[[0]],[[10758]],[[0]],[[132]]]
theorem step091 : p091=NestedHorner.scale (-1) p090 := by decide +kernel
#print axioms step091
theorem h091 : NestedArithmetic.compile e091=p091 := StagedExprCompile.compile_scaled (-1) e091 e090 p090 p091 rfl h090 step091
#print axioms h091
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
