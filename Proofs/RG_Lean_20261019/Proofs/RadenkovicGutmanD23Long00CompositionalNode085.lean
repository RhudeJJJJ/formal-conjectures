/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode073
import Proofs.RadenkovicGutmanD23Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-1656,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-14904,-129168,0],[-129168,-33810,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2281554,-1829466,0],[-1829466,-217396,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-34767306,-11069532,0],[-11069532,-657202,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-245580384,-37831550,0],[-37831550,-1071892,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1037769154,-81601516,0],[-81601516,-1005928,0],[0,0]],[[0,0,0],[0,0],[0]],[[-2925678430,-117803838,0],[-117803838,-555404],[0]],[[0,0,0],[0,0],[0]],[[-5842046828,-117733320,0],[-117733320,-177698],[0]],[[0,0,0],[0,0],[0]],[[-8571821792,-82945084,0],[-82945084,-30452],[0]],[[0,0,0],[0,0],[0]],[[-9461472142,-41429624,0],[-41429624,-2162],[0]],[[0,0,0],[0,0],[0]],[[-7973000140,-14569350,0],[-14569350,0],[0]],[[0,0],[0]],[[-5171141980,-3524060],[-3524060]],[[0,0],[0]],[[-2587525576,-557750],[-557750]],[[0,0],[0]],[[-995509598,-51980],[-51980]],[[0,0],[0]],[[-291530566,-2162],[-2162]],[[0,0],[0]],[[-63754620,0],[0]],[[0]],[[-10074920]],[[0]],[[-1086106]],[[0]],[[-71438]],[[0]],[[-2162]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
