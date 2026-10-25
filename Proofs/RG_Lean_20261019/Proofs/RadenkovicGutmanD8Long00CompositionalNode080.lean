/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode035
import Proofs.RadenkovicGutmanD8Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-192],[0,-192]],[[0,0,0],[0,0,0],[0,0]],[[0,-1728,-1728],[-1728,-6912,-832],[-1728,-832]],[[0,0,0],[0,0,0],[0,0]],[[-31104,-69120,-12096],[-69120,-48384,-1024],[-12096,-1024]],[[0,0,0],[0,0,0],[0,0]],[[-767232,-576000,-33408],[-576000,-133632,-448],[-33408,-448]],[[0,0,0],[0,0,0],[0,0]],[[-6856704,-2279296,-48448],[-2279296,-193792,-64],[-48448,-64]],[[0,0,0],[0,0],[0]],[[-33299712,-5326464,-40704],[-5326464,-162816],[-40704]],[[0,0,0],[0,0],[0]],[[-102986112,-8097792,-20416],[-8097792,-81664],[-20416]],[[0,0,0],[0,0],[0]],[[-220092416,-8417920,-6016],[-8417920,-24064],[-6016]],[[0,0,0],[0,0],[0]],[[-340893184,-6136128,-960],[-6136128,-3840],[-960]],[[0,0,0],[0,0],[0]],[[-394061696,-3163968,-64],[-3163968,-256],[-64]],[[0,0],[0]],[[-346139776,-1147456],[-1147456]],[[0,0],[0]],[[-233344896,-286080],[-286080]],[[0,0],[0]],[[-121139200,-46656],[-46656]],[[0,0],[0]],[[-48293888,-4480],[-4480]],[[0,0],[0]],[[-14641280,-192],[-192]],[[0]],[[-3312384]],[[0]],[[-541184]],[[0]],[[-60288]],[[0]],[[-4096]],[[0]],[[-128]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
