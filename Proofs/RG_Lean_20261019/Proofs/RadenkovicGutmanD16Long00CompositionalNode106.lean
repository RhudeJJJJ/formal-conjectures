/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode095
import Proofs.RadenkovicGutmanD16Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1152,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-10368,-10368,0],[-10368,-9984,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-273024,-117504,0],[-117504,-33920,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2695680,-570240,0],[-570240,-58624,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-14527104,-1570560,0],[-1570560,-56832,0],[0,0]],[[0,0,0],[0,0],[0]],[[-49645952,-2745728,0],[-2745728,-32000],[0]],[[0,0,0],[0,0],[0]],[[-116413184,-3223040,0],[-3223040,-10368],[0]],[[0,0,0],[0,0],[0]],[[-196285952,-2614528,0],[-2614528,-1792],[0]],[[0,0,0],[0,0],[0]],[[-245092224,-1482240,0],[-1482240,-128],[0]],[[0,0,0],[0,0],[0]],[[-230854400,-585088,0],[-585088,0],[0]],[[0,0],[0]],[[-165772032,-157440],[-157440]],[[0,0],[0]],[[-91123712,-27520],[-27520]],[[0,0],[0]],[[-38263168,-2816],[-2816]],[[0,0],[0]],[[-12161920,-128],[-128]],[[0,0],[0]],[[-2873088,0],[0]],[[0]],[[-488448]],[[0]],[[-56448]],[[0]],[[-3968]],[[0]],[[-128]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
