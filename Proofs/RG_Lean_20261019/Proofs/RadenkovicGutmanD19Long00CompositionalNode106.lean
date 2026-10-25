/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode095
import Proofs.RadenkovicGutmanD19Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1368,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-12312,-12312,0],[-12312,-11856,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-324216,-139536,0],[-139536,-40280,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3201120,-677160,0],[-677160,-69616,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-17250936,-1865040,0],[-1865040,-67488,0],[0,0]],[[0,0,0],[0,0],[0]],[[-58954568,-3260552,0],[-3260552,-38000],[0]],[[0,0,0],[0,0],[0]],[[-138240656,-3827360,0],[-3827360,-12312],[0]],[[0,0,0],[0,0],[0]],[[-233089568,-3104752,0],[-3104752,-2128],[0]],[[0,0,0],[0,0],[0]],[[-291047016,-1760160,0],[-1760160,-152],[0]],[[0,0,0],[0,0],[0]],[[-274139600,-694792,0],[-694792,0],[0]],[[0,0],[0]],[[-196854288,-186960],[-186960]],[[0,0],[0]],[[-108209408,-32680],[-32680]],[[0,0],[0]],[[-45437512,-3344],[-3344]],[[0,0],[0]],[[-14442280,-152],[-152]],[[0,0],[0]],[[-3411792,0],[0]],[[0]],[[-580032]],[[0]],[[-67032]],[[0]],[[-4712]],[[0]],[[-152]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
