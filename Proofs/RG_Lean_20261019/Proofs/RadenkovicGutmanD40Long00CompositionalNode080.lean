/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode035
import Proofs.RadenkovicGutmanD40Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-4800],[0,-4800]],[[0,0,0],[0,0,0],[0,0]],[[0,-43200,-43200],[-43200,-172800,-20800],[-43200,-20800]],[[0,0,0],[0,0,0],[0,0]],[[-777600,-1728000,-302400],[-1728000,-1209600,-25600],[-302400,-25600]],[[0,0,0],[0,0,0],[0,0]],[[-19180800,-14400000,-835200],[-14400000,-3340800,-11200],[-835200,-11200]],[[0,0,0],[0,0,0],[0,0]],[[-171417600,-56982400,-1211200],[-56982400,-4844800,-1600],[-1211200,-1600]],[[0,0,0],[0,0],[0]],[[-832492800,-133161600,-1017600],[-133161600,-4070400],[-1017600]],[[0,0,0],[0,0],[0]],[[-2574652800,-202444800,-510400],[-202444800,-2041600],[-510400]],[[0,0,0],[0,0],[0]],[[-5502310400,-210448000,-150400],[-210448000,-601600],[-150400]],[[0,0,0],[0,0],[0]],[[-8522329600,-153403200,-24000],[-153403200,-96000],[-24000]],[[0,0,0],[0,0],[0]],[[-9851542400,-79099200,-1600],[-79099200,-6400],[-1600]],[[0,0],[0]],[[-8653494400,-28686400],[-28686400]],[[0,0],[0]],[[-5833622400,-7152000],[-7152000]],[[0,0],[0]],[[-3028480000,-1166400],[-1166400]],[[0,0],[0]],[[-1207347200,-112000],[-112000]],[[0,0],[0]],[[-366032000,-4800],[-4800]],[[0]],[[-82809600]],[[0]],[[-13529600]],[[0]],[[-1507200]],[[0]],[[-102400]],[[0]],[[-3200]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
