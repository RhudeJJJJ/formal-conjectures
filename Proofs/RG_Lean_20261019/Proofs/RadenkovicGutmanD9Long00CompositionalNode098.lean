/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode097
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e098 : NestedArithmetic.Expr 3 := .scaled (-1) e097
noncomputable def p098 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,243],[0,243]],[[0,0,0],[0,0,0],[0,0]],[[0,-2187,3645],[-2187,10935,1107],[3645,1107]],[[0,0,0],[0,0,0],[0,0]],[[-32805,72657,28431],[72657,81972,1530],[28431,1530]],[[0,0,0],[0,0,0],[0,0]],[[193185,894240,88614],[894240,245727,855],[88614,855]],[[0,0,0],[0,0,0],[0,0]],[[5671134,4246749,144909],[4246749,389376,207],[144909,207]],[[0,0,0],[0,0,0],[0,0]],[[39696723,11309076,137070],[11309076,360216,18],[137070,18]],[[0,0,0],[0,0],[0]],[[151475211,19174725,77787],[19174725,201906],[77787]],[[0,0,0],[0,0],[0]],[[375820704,21986514,26478],[21986514,68607],[26478]],[[0,0,0],[0,0],[0]],[[655263720,17579781,5175],[17579781,13572],[5175]],[[0,0,0],[0,0],[0]],[[837537543,9929943,513],[9929943,1395],[513]],[[0,0,0],[0,0],[0]],[[804409254,3959334,18],[3959334,54],[18]],[[0,0],[0]],[[588771612,1097586],[1097586]],[[0,0],[0]],[[330529788,204282],[204282]],[[0,0],[0]],[[142312329,23832],[23832]],[[0,0],[0]],[[46682487,1512],[1512]],[[0,0],[0]],[[11498220,36],[36]],[[0]],[[2073060]],[[0]],[[262125]],[[0]],[[21573]],[[0]],[[999]],[[0]],[[18]]]
theorem step098 : p098=NestedHorner.scale (-1) p097 := by decide +kernel
#print axioms step098
theorem h098 : NestedArithmetic.compile e098=p098 := StagedExprCompile.compile_scaled (-1) e098 e097 p097 p098 rfl h097 step098
#print axioms h098
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
