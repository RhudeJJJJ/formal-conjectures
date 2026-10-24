/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode073
import Proofs.RadenkovicGutmanD5Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-360,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3240,-8640,0],[-8640,-4110,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-175230,-115830,0],[-115830,-19180,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2319030,-669780,0],[-669780,-47470,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-15323520,-2206850,0],[-2206850,-68140,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-62073790,-4623940,0],[-4623940,-58840,0],[0,0]],[[0,0,0],[0,0],[0]],[[-169770610,-6523410,0],[-6523410,-30740],[0]],[[0,0,0],[0,0],[0]],[[-331211540,-6400440,0],[-6400440,-9470],[0]],[[0,0,0],[0,0],[0]],[[-477037760,-4442260,0],[-4442260,-1580],[0]],[[0,0,0],[0,0],[0]],[[-518583730,-2191640,0],[-2191640,-110],[0]],[[0,0,0],[0,0],[0]],[[-431452660,-762810,0],[-762810,0],[0]],[[0,0],[0]],[[-276804100,-182900],[-182900]],[[0,0],[0]],[[-137213080,-28730],[-28730]],[[0,0],[0]],[[-52360610,-2660],[-2660]],[[0,0],[0]],[[-15223690,-110],[-110]],[[0,0],[0]],[[-3308100,0],[0]],[[0]],[[-519800]],[[0]],[[-55750]],[[0]],[[-3650]],[[0]],[[-110]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
