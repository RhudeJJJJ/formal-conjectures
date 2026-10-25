/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode035
import Proofs.RadenkovicGutmanD7Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-147],[0,-147]],[[0,0,0],[0,0,0],[0,0]],[[0,-1323,-1323],[-1323,-5292,-637],[-1323,-637]],[[0,0,0],[0,0,0],[0,0]],[[-23814,-52920,-9261],[-52920,-37044,-784],[-9261,-784]],[[0,0,0],[0,0,0],[0,0]],[[-587412,-441000,-25578],[-441000,-102312,-343],[-25578,-343]],[[0,0,0],[0,0,0],[0,0]],[[-5249664,-1745086,-37093],[-1745086,-148372,-49],[-37093,-49]],[[0,0,0],[0,0],[0]],[[-25495092,-4078074,-31164],[-4078074,-124656],[-31164]],[[0,0,0],[0,0],[0]],[[-78848742,-6199872,-15631],[-6199872,-62524],[-15631]],[[0,0,0],[0,0],[0]],[[-168508256,-6444970,-4606],[-6444970,-18424],[-4606]],[[0,0,0],[0,0],[0]],[[-260996344,-4697973,-735],[-4697973,-2940],[-735]],[[0,0,0],[0,0],[0]],[[-301703486,-2422413,-49],[-2422413,-196],[-49]],[[0,0],[0]],[[-265013266,-878521],[-878521]],[[0,0],[0]],[[-178654686,-219030],[-219030]],[[0,0],[0]],[[-92747200,-35721],[-35721]],[[0,0],[0]],[[-36975008,-3430],[-3430]],[[0,0],[0]],[[-11209730,-147],[-147]],[[0]],[[-2536044]],[[0]],[[-414344]],[[0]],[[-46158]],[[0]],[[-3136]],[[0]],[[-98]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
