/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode035
import Proofs.RadenkovicGutmanD30Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e076 : NestedArithmetic.Expr 3 := .times e035 e074
noncomputable def p076 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,-8100],[0,-16200],[-8100]],[[0,0,0],[0,0],[0]],[[0,-267300,-70200],[-267300,-140400],[-70200]],[[0,0,0],[0,0],[0]],[[-2187000,-2988900,-238500],[-2988900,-477000],[-238500]],[[0,0,0],[0,0],[0]],[[-29889000,-14280300,-412200],[-14280300,-824400],[-412200]],[[0,0,0],[0,0],[0]],[[-182201400,-38655000,-399600],[-38655000,-799200],[-399600]],[[0,0,0],[0,0],[0]],[[-659534400,-66350700,-225000],[-66350700,-450000],[-225000]],[[0,0,0],[0,0],[0]],[[-1591736400,-76443300,-72900],[-76443300,-145800],[-72900]],[[0,0,0],[0,0],[0]],[[-2723504400,-60872400,-12600],[-60872400,-25200],[-12600]],[[0,0,0],[0,0],[0]],[[-3425765400,-33893100,-900],[-33893100,-1800],[-900]],[[0,0],[0]],[[-3238162200,-13148100],[-13148100]],[[0,0],[0]],[[-2328955200,-3479400],[-3479400]],[[0,0],[0]],[[-1281040200,-598500],[-598500]],[[0,0],[0]],[[-538036200,-60300],[-60300]],[[0,0],[0]],[[-171025200,-2700],[-2700]],[[0]],[[-40402800]],[[0]],[[-6868800]],[[0]],[[-793800]],[[0]],[[-55800]],[[0]],[[-1800]]]
theorem step076 : p076=NestedArithmetic.mul p035 p074 := by decide +kernel
#print axioms step076
theorem h076 : NestedArithmetic.compile e076=p076 := StagedExprCompile.compile_times e076 e035 e074 p035 p074 p076 rfl h035 h074 step076
#print axioms h076
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
