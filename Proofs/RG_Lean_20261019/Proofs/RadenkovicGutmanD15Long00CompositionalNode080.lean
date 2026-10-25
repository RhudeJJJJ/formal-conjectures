/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode035
import Proofs.RadenkovicGutmanD15Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-675],[0,-675]],[[0,0,0],[0,0,0],[0,0]],[[0,-6075,-6075],[-6075,-24300,-2925],[-6075,-2925]],[[0,0,0],[0,0,0],[0,0]],[[-109350,-243000,-42525],[-243000,-170100,-3600],[-42525,-3600]],[[0,0,0],[0,0,0],[0,0]],[[-2697300,-2025000,-117450],[-2025000,-469800,-1575],[-117450,-1575]],[[0,0,0],[0,0,0],[0,0]],[[-24105600,-8013150,-170325],[-8013150,-681300,-225],[-170325,-225]],[[0,0,0],[0,0],[0]],[[-117069300,-18725850,-143100],[-18725850,-572400],[-143100]],[[0,0,0],[0,0],[0]],[[-362060550,-28468800,-71775],[-28468800,-287100],[-71775]],[[0,0,0],[0,0],[0]],[[-773762400,-29594250,-21150],[-29594250,-84600],[-21150]],[[0,0,0],[0,0],[0]],[[-1198452600,-21572325,-3375],[-21572325,-13500],[-3375]],[[0,0,0],[0,0],[0]],[[-1385373150,-11123325,-225],[-11123325,-900],[-225]],[[0,0],[0]],[[-1216897650,-4034025],[-4034025]],[[0,0],[0]],[[-820353150,-1005750],[-1005750]],[[0,0],[0]],[[-425880000,-164025],[-164025]],[[0,0],[0]],[[-169783200,-15750],[-15750]],[[0,0],[0]],[[-51473250,-675],[-675]],[[0]],[[-11645100]],[[0]],[[-1902600]],[[0]],[[-211950]],[[0]],[[-14400]],[[0]],[[-450]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
