/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode035
import Proofs.RadenkovicGutmanD45Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-6075],[0,-6075]],[[0,0,0],[0,0,0],[0,0]],[[0,-54675,-54675],[-54675,-218700,-26325],[-54675,-26325]],[[0,0,0],[0,0,0],[0,0]],[[-984150,-2187000,-382725],[-2187000,-1530900,-32400],[-382725,-32400]],[[0,0,0],[0,0,0],[0,0]],[[-24275700,-18225000,-1057050],[-18225000,-4228200,-14175],[-1057050,-14175]],[[0,0,0],[0,0,0],[0,0]],[[-216950400,-72118350,-1532925],[-72118350,-6131700,-2025],[-1532925,-2025]],[[0,0,0],[0,0],[0]],[[-1053623700,-168532650,-1287900],[-168532650,-5151600],[-1287900]],[[0,0,0],[0,0],[0]],[[-3258544950,-256219200,-645975],[-256219200,-2583900],[-645975]],[[0,0,0],[0,0],[0]],[[-6963861600,-266348250,-190350],[-266348250,-761400],[-190350]],[[0,0,0],[0,0],[0]],[[-10786073400,-194150925,-30375],[-194150925,-121500],[-30375]],[[0,0,0],[0,0],[0]],[[-12468358350,-100109925,-2025],[-100109925,-8100],[-2025]],[[0,0],[0]],[[-10952078850,-36306225],[-36306225]],[[0,0],[0]],[[-7383178350,-9051750],[-9051750]],[[0,0],[0]],[[-3832920000,-1476225],[-1476225]],[[0,0],[0]],[[-1528048800,-141750],[-141750]],[[0,0],[0]],[[-463259250,-6075],[-6075]],[[0]],[[-104805900]],[[0]],[[-17123400]],[[0]],[[-1907550]],[[0]],[[-129600]],[[0]],[[-4050]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
