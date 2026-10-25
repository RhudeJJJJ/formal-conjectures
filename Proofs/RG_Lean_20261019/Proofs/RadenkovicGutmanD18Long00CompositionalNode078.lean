/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode075
import Proofs.RadenkovicGutmanD18Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,324]],[[0,0],[0,0,0],[0,0]],[[0,0,2916],[0,5832,5832],[2916,5832]],[[0,0,0],[0,0,0],[0,0]],[[-26244,96228,51516],[96228,155520,15552],[51516,15552]],[[0,0,0],[0,0,0],[0,0]],[[332424,1548396,225828],[1548396,731592,14256],[225828,14256]],[[0,0,0],[0,0,0],[0,0]],[[9369108,8920044,463320],[8920044,1556496,5184],[463320,5184]],[[0,0,0],[0,0,0],[0,0]],[[72202104,27457704,532656],[27457704,1842912,648],[532656,648]],[[0,0,0],[0,0],[0]],[[300425436,52579692,368064],[52579692,1310256],[368064]],[[0,0,0],[0,0],[0]],[[805561200,67497948,155844],[67497948,570888],[155844]],[[0,0,0],[0,0],[0]],[[1511683560,60451920,39528],[60451920,149040],[39528]],[[0,0,0],[0,0],[0]],[[2079243432,38533644,5508],[38533644,21384],[5508]],[[0,0,0],[0,0],[0]],[[2155303080,17579268,324],[17579268,1296],[324]],[[0,0],[0]],[[1711970640,5694624],[5694624]],[[0,0],[0]],[[1051227720,1278180],[1278180]],[[0,0],[0]],[[500235912,188892],[188892]],[[0,0],[0]],[[183804876,16524],[16524]],[[0,0],[0]],[[51605424,648],[648]],[[0]],[[10857240]],[[0]],[[1655640]],[[0]],[[172692]],[[0]],[[11016]],[[0]],[[324]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
