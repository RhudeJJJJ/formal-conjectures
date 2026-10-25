/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode079
import Proofs.RadenkovicGutmanD30Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-48600,0],[-48600,-8100,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-801900,-704700,0],[-704700,-70200,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-13097700,-4341600,0],[-4341600,-238500,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-95158800,-15043500,0],[-15043500,-412200,0],[0,0]],[[0,0,0],[0,0],[0]],[[-408820500,-32788800,0],[-32788800,-399600],[0]],[[0,0,0],[0,0],[0]],[[-1165616100,-47715300,0],[-47715300,-225000],[0]],[[0,0,0],[0,0],[0]],[[-2346996600,-47984400,0],[-47984400,-72900],[0]],[[0,0,0],[0,0],[0]],[[-3466004400,-33973200,0],[-33973200,-12600],[0]],[[0,0,0],[0,0],[0]],[[-3845645100,-17037000,0],[-17037000,-900],[0]],[[0,0],[0]],[[-3254520600,-6011100],[-6011100]],[[0,0],[0]],[[-2118393000,-1458000],[-1458000]],[[0,0],[0]],[[-1063231200,-231300],[-231300]],[[0,0],[0]],[[-410136300,-21600],[-21600]],[[0,0],[0]],[[-120381300,-900],[-900]],[[0]],[[-26379000]],[[0]],[[-4176000]],[[0]],[[-450900]],[[0]],[[-29700]],[[0]],[[-900]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
