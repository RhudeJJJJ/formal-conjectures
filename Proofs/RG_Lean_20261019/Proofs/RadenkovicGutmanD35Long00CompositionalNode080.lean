/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode035
import Proofs.RadenkovicGutmanD35Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-3675],[0,-3675]],[[0,0,0],[0,0,0],[0,0]],[[0,-33075,-33075],[-33075,-132300,-15925],[-33075,-15925]],[[0,0,0],[0,0,0],[0,0]],[[-595350,-1323000,-231525],[-1323000,-926100,-19600],[-231525,-19600]],[[0,0,0],[0,0,0],[0,0]],[[-14685300,-11025000,-639450],[-11025000,-2557800,-8575],[-639450,-8575]],[[0,0,0],[0,0,0],[0,0]],[[-131241600,-43627150,-927325],[-43627150,-3709300,-1225],[-927325,-1225]],[[0,0,0],[0,0],[0]],[[-637377300,-101951850,-779100],[-101951850,-3116400],[-779100]],[[0,0,0],[0,0],[0]],[[-1971218550,-154996800,-390775],[-154996800,-1563100],[-390775]],[[0,0,0],[0,0],[0]],[[-4212706400,-161124250,-115150],[-161124250,-460600],[-115150]],[[0,0,0],[0,0],[0]],[[-6524908600,-117449325,-18375],[-117449325,-73500],[-18375]],[[0,0,0],[0,0],[0]],[[-7542587150,-60560325,-1225],[-60560325,-4900],[-1225]],[[0,0],[0]],[[-6625331650,-21963025],[-21963025]],[[0,0],[0]],[[-4466367150,-5475750],[-5475750]],[[0,0],[0]],[[-2318680000,-893025],[-893025]],[[0,0],[0]],[[-924375200,-85750],[-85750]],[[0,0],[0]],[[-280243250,-3675],[-3675]],[[0]],[[-63401100]],[[0]],[[-10358600]],[[0]],[[-1153950]],[[0]],[[-78400]],[[0]],[[-2450]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
