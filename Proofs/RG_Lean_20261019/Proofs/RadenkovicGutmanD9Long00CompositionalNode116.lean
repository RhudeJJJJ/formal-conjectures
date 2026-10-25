/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode115
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e116 : NestedArithmetic.Expr 3 := .scaled (-1) e115
noncomputable def p116 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,-81]],[[0,0],[0,0,0],[0,0]],[[0,0,-729],[0,0,-1458],[-729,-1458]],[[0,0,0],[0,0,0],[0,0]],[[-6561,-13122,-12879],[-13122,-26244,-3888],[-12879,-3888]],[[0,0,0],[0,0,0],[0,0]],[[-231822,-266814,-56457],[-266814,-139968,-3564],[-56457,-3564]],[[0,0,0],[0,0,0],[0,0]],[[-3063987,-1666494,-115830],[-1666494,-314928,-1296],[-115830,-1296]],[[0,0,0],[0,0,0],[0,0]],[[-20038266,-5373216,-133164],[-5373216,-388800,-162],[-133164,-162]],[[0,0,0],[0,0],[0]],[[-78581421,-10648422,-92016],[-10648422,-287064],[-92016]],[[0,0,0],[0,0],[0]],[[-205469460,-14073750,-38961],[-14073750,-129600],[-38961]],[[0,0,0],[0,0],[0]],[[-381229902,-12943476,-9882],[-12943476,-34992],[-9882]],[[0,0,0],[0,0],[0]],[[-521686818,-8458992,-1377],[-8458992,-5184],[-1377]],[[0,0,0],[0,0],[0]],[[-539566272,-3951990,-81],[-3951990,-324],[-81]],[[0,0],[0]],[[-428191920,-1309770],[-1309770]],[[0,0],[0]],[[-262841760,-300510],[-300510]],[[0,0],[0]],[[-125062542,-45360],[-45360]],[[0,0],[0]],[[-45951381,-4050],[-4050]],[[0,0],[0]],[[-12901356,-162],[-162]],[[0]],[[-2714310]],[[0]],[[-413910]],[[0]],[[-43173]],[[0]],[[-2754]],[[0]],[[-81]]]
theorem step116 : p116=NestedHorner.scale (-1) p115 := by decide +kernel
#print axioms step116
theorem h116 : NestedArithmetic.compile e116=p116 := StagedExprCompile.compile_scaled (-1) e116 e115 p115 p116 rfl h115 step116
#print axioms h116
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
