/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode043
import Proofs.RadenkovicGutmanD6Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,108],[0,108,-48]],[[0,0,0],[0,0,0],[0,0]],[[0,972,972],[972,4320,-396],[972,-396]],[[0,0,0],[0,0,0],[0,0]],[[25272,42768,2916],[42768,15408,-1728],[2916,-1728]],[[0,0,0],[0,0,0],[0,0]],[[601344,298080,-1944],[298080,4944,-1860],[-1944,-1860]],[[0,0,0],[0,0,0],[0,0]],[[5073840,936072,-19404],[936072,-55632,-732],[-19404,-732]],[[0,0,0],[0,0,0],[0,0]],[[23199552,1578888,-34704],[1578888,-117504,-96],[-34704,-96]],[[0,0,0],[0,0],[0]],[[67214616,1333776,-31044],[1333776,-112176],[-31044]],[[0,0,0],[0,0],[0]],[[133007136,21000,-15816],[21000,-59376],[-15816]],[[0,0,0],[0,0],[0]],[[186660096,-1277292,-4644],[-1277292,-17904],[-4644]],[[0,0,0],[0,0],[0]],[[188240712,-1565484,-732],[-1565484,-2880],[-732]],[[0,0,0],[0,0],[0]],[[134671848,-1038252,-48],[-1038252,-192],[-48]],[[0,0],[0]],[[64006680,-438120],[-438120]],[[0,0],[0]],[[14896896,-120876],[-120876]],[[0,0],[0]],[[-3899760,-21192],[-21192]],[[0,0],[0]],[[-5312568,-2148],[-2148]],[[0,0],[0]],[[-2549808,-96],[-96]],[[0]],[[-754560]],[[0]],[[-147864]],[[0]],[[-18816]],[[0]],[[-1416]],[[0]],[[-48]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
