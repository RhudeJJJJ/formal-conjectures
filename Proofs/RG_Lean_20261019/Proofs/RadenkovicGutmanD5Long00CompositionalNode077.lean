/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode076
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e077 : NestedArithmetic.Expr 3 := .scaled (-1) e076
noncomputable def p077 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,225],[0,450],[225]],[[0,0,0],[0,0],[0]],[[0,7425,1950],[7425,3900],[1950]],[[0,0,0],[0,0],[0]],[[60750,83025,6625],[83025,13250],[6625]],[[0,0,0],[0,0],[0]],[[830250,396675,11450],[396675,22900],[11450]],[[0,0,0],[0,0],[0]],[[5061150,1073750,11100],[1073750,22200],[11100]],[[0,0,0],[0,0],[0]],[[18320400,1843075,6250],[1843075,12500],[6250]],[[0,0,0],[0,0],[0]],[[44214900,2123425,2025],[2123425,4050],[2025]],[[0,0,0],[0,0],[0]],[[75652900,1690900,350],[1690900,700],[350]],[[0,0,0],[0,0],[0]],[[95160150,941475,25],[941475,50],[25]],[[0,0],[0]],[[89948950,365225],[365225]],[[0,0],[0]],[[64693200,96650],[96650]],[[0,0],[0]],[[35584450,16625],[16625]],[[0,0],[0]],[[14945450,1675],[1675]],[[0,0],[0]],[[4750700,75],[75]],[[0]],[[1122300]],[[0]],[[190800]],[[0]],[[22050]],[[0]],[[1550]],[[0]],[[50]]]
theorem step077 : p077=NestedHorner.scale (-1) p076 := by decide +kernel
#print axioms step077
theorem h077 : NestedArithmetic.compile e077=p077 := StagedExprCompile.compile_scaled (-1) e077 e076 p076 p077 rfl h076 step077
#print axioms h077
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
