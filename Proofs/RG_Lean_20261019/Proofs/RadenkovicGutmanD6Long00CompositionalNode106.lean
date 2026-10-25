/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode095
import Proofs.RadenkovicGutmanD6Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-432,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3888,-3888,0],[-3888,-3744,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-102384,-44064,0],[-44064,-12720,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1010880,-213840,0],[-213840,-21984,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5447664,-588960,0],[-588960,-21312,0],[0,0]],[[0,0,0],[0,0],[0]],[[-18617232,-1029648,0],[-1029648,-12000],[0]],[[0,0,0],[0,0],[0]],[[-43654944,-1208640,0],[-1208640,-3888],[0]],[[0,0,0],[0,0],[0]],[[-73607232,-980448,0],[-980448,-672],[0]],[[0,0,0],[0,0],[0]],[[-91909584,-555840,0],[-555840,-48],[0]],[[0,0,0],[0,0],[0]],[[-86570400,-219408,0],[-219408,0],[0]],[[0,0],[0]],[[-62164512,-59040],[-59040]],[[0,0],[0]],[[-34171392,-10320],[-10320]],[[0,0],[0]],[[-14348688,-1056],[-1056]],[[0,0],[0]],[[-4560720,-48],[-48]],[[0,0],[0]],[[-1077408,0],[0]],[[0]],[[-183168]],[[0]],[[-21168]],[[0]],[[-1488]],[[0]],[[-48]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
