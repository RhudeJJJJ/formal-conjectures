/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode035
import Proofs.RadenkovicGutmanD27Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-2187],[0,-2187]],[[0,0,0],[0,0,0],[0,0]],[[0,-19683,-19683],[-19683,-78732,-9477],[-19683,-9477]],[[0,0,0],[0,0,0],[0,0]],[[-354294,-787320,-137781],[-787320,-551124,-11664],[-137781,-11664]],[[0,0,0],[0,0,0],[0,0]],[[-8739252,-6561000,-380538],[-6561000,-1522152,-5103],[-380538,-5103]],[[0,0,0],[0,0,0],[0,0]],[[-78102144,-25962606,-551853],[-25962606,-2207412,-729],[-551853,-729]],[[0,0,0],[0,0],[0]],[[-379304532,-60671754,-463644],[-60671754,-1854576],[-463644]],[[0,0,0],[0,0],[0]],[[-1173076182,-92238912,-232551],[-92238912,-930204],[-232551]],[[0,0,0],[0,0],[0]],[[-2506990176,-95885370,-68526],[-95885370,-274104],[-68526]],[[0,0,0],[0,0],[0]],[[-3882986424,-69894333,-10935],[-69894333,-43740],[-10935]],[[0,0,0],[0,0],[0]],[[-4488609006,-36039573,-729],[-36039573,-2916],[-729]],[[0,0],[0]],[[-3942748386,-13070241],[-13070241]],[[0,0],[0]],[[-2657944206,-3258630],[-3258630]],[[0,0],[0]],[[-1379851200,-531441],[-531441]],[[0,0],[0]],[[-550097568,-51030],[-51030]],[[0,0],[0]],[[-166773330,-2187],[-2187]],[[0]],[[-37730124]],[[0]],[[-6164424]],[[0]],[[-686718]],[[0]],[[-46656]],[[0]],[[-1458]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
