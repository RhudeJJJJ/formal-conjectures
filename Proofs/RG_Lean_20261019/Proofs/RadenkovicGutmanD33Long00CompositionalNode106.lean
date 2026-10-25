/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode095
import Proofs.RadenkovicGutmanD33Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2376,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-21384,-21384,0],[-21384,-20592,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-563112,-242352,0],[-242352,-69960,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5559840,-1176120,0],[-1176120,-120912,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-29962152,-3239280,0],[-3239280,-117216,0],[0,0]],[[0,0,0],[0,0],[0]],[[-102394776,-5663064,0],[-5663064,-66000],[0]],[[0,0,0],[0,0],[0]],[[-240102192,-6647520,0],[-6647520,-21384],[0]],[[0,0,0],[0,0],[0]],[[-404839776,-5392464,0],[-5392464,-3696],[0]],[[0,0,0],[0,0],[0]],[[-505502712,-3057120,0],[-3057120,-264],[0]],[[0,0,0],[0,0],[0]],[[-476137200,-1206744,0],[-1206744,0],[0]],[[0,0],[0]],[[-341904816,-324720],[-324720]],[[0,0],[0]],[[-187942656,-56760],[-56760]],[[0,0],[0]],[[-78917784,-5808],[-5808]],[[0,0],[0]],[[-25083960,-264],[-264]],[[0,0],[0]],[[-5925744,0],[0]],[[0]],[[-1007424]],[[0]],[[-116424]],[[0]],[[-8184]],[[0]],[[-264]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
