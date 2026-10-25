/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode078
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e082 : NestedArithmetic.Expr 3 := .scaled (-1) e078
noncomputable def p082 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,-81]],[[0,0],[0,0,0],[0,0]],[[0,0,-729],[0,-1458,-1458],[-729,-1458]],[[0,0,0],[0,0,0],[0,0]],[[6561,-24057,-12879],[-24057,-38880,-3888],[-12879,-3888]],[[0,0,0],[0,0,0],[0,0]],[[-83106,-387099,-56457],[-387099,-182898,-3564],[-56457,-3564]],[[0,0,0],[0,0,0],[0,0]],[[-2342277,-2230011,-115830],[-2230011,-389124,-1296],[-115830,-1296]],[[0,0,0],[0,0,0],[0,0]],[[-18050526,-6864426,-133164],[-6864426,-460728,-162],[-133164,-162]],[[0,0,0],[0,0],[0]],[[-75106359,-13144923,-92016],[-13144923,-327564],[-92016]],[[0,0,0],[0,0],[0]],[[-201390300,-16874487,-38961],[-16874487,-142722],[-38961]],[[0,0,0],[0,0],[0]],[[-377920890,-15112980,-9882],[-15112980,-37260],[-9882]],[[0,0,0],[0,0],[0]],[[-519810858,-9633411,-1377],[-9633411,-5346],[-1377]],[[0,0,0],[0,0],[0]],[[-538825770,-4394817,-81],[-4394817,-324],[-81]],[[0,0],[0]],[[-427992660,-1423656],[-1423656]],[[0,0],[0]],[[-262806930,-319545],[-319545]],[[0,0],[0]],[[-125058978,-47223],[-47223]],[[0,0],[0]],[[-45951219,-4131],[-4131]],[[0,0],[0]],[[-12901356,-162],[-162]],[[0]],[[-2714310]],[[0]],[[-413910]],[[0]],[[-43173]],[[0]],[[-2754]],[[0]],[[-81]]]
theorem step082 : p082=NestedHorner.scale (-1) p078 := by decide +kernel
#print axioms step082
theorem h082 : NestedArithmetic.compile e082=p082 := StagedExprCompile.compile_scaled (-1) e082 e078 p078 p082 rfl h078 step082
#print axioms h082
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
