/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode095
import Proofs.RadenkovicGutmanD32Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2304,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-20736,-20736,0],[-20736,-19968,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-546048,-235008,0],[-235008,-67840,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5391360,-1140480,0],[-1140480,-117248,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-29054208,-3141120,0],[-3141120,-113664,0],[0,0]],[[0,0,0],[0,0],[0]],[[-99291904,-5491456,0],[-5491456,-64000],[0]],[[0,0,0],[0,0],[0]],[[-232826368,-6446080,0],[-6446080,-20736],[0]],[[0,0,0],[0,0],[0]],[[-392571904,-5229056,0],[-5229056,-3584],[0]],[[0,0,0],[0,0],[0]],[[-490184448,-2964480,0],[-2964480,-256],[0]],[[0,0,0],[0,0],[0]],[[-461708800,-1170176,0],[-1170176,0],[0]],[[0,0],[0]],[[-331544064,-314880],[-314880]],[[0,0],[0]],[[-182247424,-55040],[-55040]],[[0,0],[0]],[[-76526336,-5632],[-5632]],[[0,0],[0]],[[-24323840,-256],[-256]],[[0,0],[0]],[[-5746176,0],[0]],[[0]],[[-976896]],[[0]],[[-112896]],[[0]],[[-7936]],[[0]],[[-256]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
