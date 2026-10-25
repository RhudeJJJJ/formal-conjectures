/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode033
import Proofs.RadenkovicGutmanD6Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,108],[0,108,-48]],[[0,0,0],[0,0,0],[0,0]],[[0,-972,972],[-972,3564,-396],[972,-396]],[[0,0,0],[0,0,0],[0,0]],[[-10692,10692,2916],[10692,8856,-1728],[2916,-1728]],[[0,0,0],[0,0,0],[0,0]],[[-24948,80352,-1944],[80352,-17316,-1860],[-1944,-1860]],[[0,0,0],[0,0,0],[0,0]],[[256608,120492,-19404],[120492,-94104,-732],[-19404,-732]],[[0,0,0],[0,0,0],[0,0]],[[1399068,-321624,-34704],[-321624,-154800,-96],[-34704,-96]],[[0,0,0],[0,0],[0]],[[1972740,-1604484,-31044],[-1604484,-133176],[-31044]],[[0,0,0],[0,0],[0]],[[-4527672,-3107016,-15816],[-3107016,-66180],[-15816]],[[0,0,0],[0,0],[0]],[[-25587312,-3616668,-4644],[-3616668,-19080],[-4644]],[[0,0,0],[0,0],[0]],[[-57494676,-2802804,-732],[-2802804,-2964],[-732]],[[0,0,0],[0,0],[0]],[[-82079376,-1498104,-48],[-1498104,-192],[-48]],[[0,0],[0]],[[-82893552,-555480],[-555480]],[[0,0],[0]],[[-61803744,-140448],[-140448]],[[0,0],[0]],[[-34653900,-23112],[-23112]],[[0,0],[0]],[[-14688540,-2232],[-2232]],[[0,0],[0]],[[-4682376,-96],[-96]],[[0]],[[-1104768]],[[0]],[[-187068]],[[0]],[[-21492]],[[0]],[[-1500]],[[0]],[[-48]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
