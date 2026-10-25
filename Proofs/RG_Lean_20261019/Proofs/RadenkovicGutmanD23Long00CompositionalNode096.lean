/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode043
import Proofs.RadenkovicGutmanD23Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1587],[0,1587,-966]],[[0,0,0],[0,0,0],[0,0]],[[0,14283,14283],[14283,58788,-10511],[14283,-10511]],[[0,0,0],[0,0,0],[0,0]],[[350244,586224,21735],[586224,101292,-37904],[21735,-37904]],[[0,0,0],[0,0,0],[0,0]],[[8090388,3521484,-141174],[3521484,-515936,-38801],[-141174,-38801]],[[0,0,0],[0,0,0],[0,0]],[[64697022,8392102,-538499],[8392102,-2069724,-14927],[-538499,-14927]],[[0,0,0],[0,0,0],[0,0]],[[276419244,5909298,-822756],[5909298,-3209328,-1932],[-822756,-1932]],[[0,0,0],[0,0],[0]],[[734798020,-14668664,-687125],[-14668664,-2702500],[-687125]],[[0,0,0],[0,0],[0]],[[1293243264,-44982250,-336674],[-44982250,-1331792],[-336674]],[[0,0,0],[0,0],[0]],[[1516027796,-60422587,-96393],[-60422587,-382996],[-96393]],[[0,0,0],[0,0],[0]],[[1087248686,-50225859,-14927],[-50225859,-59524],[-14927]],[[0,0,0],[0,0],[0]],[[242545994,-27974463,-966],[-27974463,-3864],[-966]],[[0,0],[0]],[[-437424810,-10652910],[-10652910]],[[0,0],[0]],[[-626951296,-2743279],[-2743279]],[[0,0],[0]],[[-459769448,-457378],[-457378]],[[0,0],[0]],[[-225941696,-44597],[-44597]],[[0,0],[0]],[[-78985956,-1932],[-1932]],[[0]],[[-19822780]],[[0]],[[-3504786]],[[0]],[[-415426]],[[0]],[[-29670]],[[0]],[[-966]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
