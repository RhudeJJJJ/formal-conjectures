/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode071
import Proofs.RadenkovicGutmanD37Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-73926,0],[-73926,-14985,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1243755,-1391607,0],[-1391607,-179820,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-25439535,-11169486,0],[-11169486,-874125,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-230830938,-50685671,0],[-50685671,-2233320,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1236002205,-145368338,0],[-145368338,-3281160,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4383681967,-279339381,0],[-279339381,-2880450,0],[0,0]],[[0,0,0],[0,0],[0]],[[-10960076064,-372351350,0],[-372351350,-1522365],[0]],[[0,0,0],[0,0],[0]],[[-20073560864,-351544844,0],[-351544844,-472860],[0]],[[0,0,0],[0,0],[0]],[[-27618618291,-237562422,0],[-237562422,-79365],[0]],[[0,0,0],[0,0],[0]],[[-29024646152,-115014167,0],[-115014167,-5550],[0]],[[0,0,0],[0,0],[0]],[[-23541071438,-39494318,0],[-39494318,0],[0]],[[0,0],[0]],[[-14813097852,-9377613],[-9377613]],[[0,0],[0]],[[-7234198523,-1462610],[-1462610]],[[0,0],[0]],[[-2728810199,-134717],[-134717]],[[0,0],[0]],[[-786253848,-5550],[-5550]],[[0,0],[0]],[[-169644260,0],[0]],[[0]],[[-26507429]],[[0]],[[-2830463]],[[0]],[[-184667]],[[0]],[[-5550]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
