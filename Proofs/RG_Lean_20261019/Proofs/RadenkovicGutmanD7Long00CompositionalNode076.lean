/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode035
import Proofs.RadenkovicGutmanD7Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e076 : NestedArithmetic.Expr 3 := .times e035 e074
noncomputable def p076 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,-441],[0,-882],[-441]],[[0,0,0],[0,0],[0]],[[0,-14553,-3822],[-14553,-7644],[-3822]],[[0,0,0],[0,0],[0]],[[-119070,-162729,-12985],[-162729,-25970],[-12985]],[[0,0,0],[0,0],[0]],[[-1627290,-777483,-22442],[-777483,-44884],[-22442]],[[0,0,0],[0,0],[0]],[[-9919854,-2104550,-21756],[-2104550,-43512],[-21756]],[[0,0,0],[0,0],[0]],[[-35907984,-3612427,-12250],[-3612427,-24500],[-12250]],[[0,0,0],[0,0],[0]],[[-86661204,-4161913,-3969],[-4161913,-7938],[-3969]],[[0,0,0],[0,0],[0]],[[-148279684,-3314164,-686],[-3314164,-1372],[-686]],[[0,0,0],[0,0],[0]],[[-186513894,-1845291,-49],[-1845291,-98],[-49]],[[0,0],[0]],[[-176299942,-715841],[-715841]],[[0,0],[0]],[[-126798672,-189434],[-189434]],[[0,0],[0]],[[-69745522,-32585],[-32585]],[[0,0],[0]],[[-29293082,-3283],[-3283]],[[0,0],[0]],[[-9311372,-147],[-147]],[[0]],[[-2199708]],[[0]],[[-373968]],[[0]],[[-43218]],[[0]],[[-3038]],[[0]],[[-98]]]
theorem step076 : p076=NestedArithmetic.mul p035 p074 := by decide +kernel
#print axioms step076
theorem h076 : NestedArithmetic.compile e076=p076 := StagedExprCompile.compile_times e076 e035 e074 p035 p074 p076 rfl h035 h074 step076
#print axioms h076
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
