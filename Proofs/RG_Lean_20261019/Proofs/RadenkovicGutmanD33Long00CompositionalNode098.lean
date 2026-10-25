/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode097
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e098 : NestedArithmetic.Expr 3 := .scaled (-1) e097
noncomputable def p098 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3267],[0,3267]],[[0,0,0],[0,0,0],[0,0]],[[0,-29403,49005],[-29403,147015,14355],[49005,14355]],[[0,0,0],[0,0,0],[0,0]],[[-441045,972081,377487],[972081,1084644,18282],[377487,18282]],[[0,0,0],[0,0,0],[0,0]],[[2525985,11846736,1158102],[11846736,3184335,8679],[1158102,8679]],[[0,0,0],[0,0,0],[0,0]],[[74510766,55672749,1856349],[55672749,4914096,1551],[1856349,1551]],[[0,0,0],[0,0,0],[0,0]],[[518551011,146560260,1709598],[146560260,4390584,66],[1709598,66]],[[0,0,0],[0,0],[0]],[[1964900619,245305269,933867],[245305269,2344914],[933867]],[[0,0,0],[0,0],[0]],[[4837751952,277102914,299838],[277102914,741807],[299838]],[[0,0,0],[0,0],[0]],[[8364470664,217632789,53031],[217632789,130548],[53031]],[[0,0,0],[0,0],[0]],[[10592663895,120223191,4257],[120223191,10659],[4257]],[[0,0,0],[0,0],[0]],[[10068167670,46568214,66],[46568214,198],[66]],[[0,0],[0]],[[7281247644,12405426],[12405426]],[[0,0],[0]],[[4030027452,2176218],[2176218]],[[0,0],[0]],[[1705472505,229944],[229944]],[[0,0],[0]],[[547423767,11880],[11880]],[[0,0],[0]],[[131046300,132],[132]],[[0]],[[22712580]],[[0]],[[2707485]],[[0]],[[201861]],[[0]],[[7623]],[[0]],[[66]]]
theorem step098 : p098=NestedHorner.scale (-1) p097 := by decide +kernel
#print axioms step098
theorem h098 : NestedArithmetic.compile e098=p098 := StagedExprCompile.compile_scaled (-1) e098 e097 p097 p098 rfl h097 step098
#print axioms h098
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
