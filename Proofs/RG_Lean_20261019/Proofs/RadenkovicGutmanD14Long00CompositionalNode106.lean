/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode095
import Proofs.RadenkovicGutmanD14Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1008,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-9072,-9072,0],[-9072,-8736,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-238896,-102816,0],[-102816,-29680,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2358720,-498960,0],[-498960,-51296,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-12711216,-1374240,0],[-1374240,-49728,0],[0,0]],[[0,0,0],[0,0],[0]],[[-43440208,-2402512,0],[-2402512,-28000],[0]],[[0,0,0],[0,0],[0]],[[-101861536,-2820160,0],[-2820160,-9072],[0]],[[0,0,0],[0,0],[0]],[[-171750208,-2287712,0],[-2287712,-1568],[0]],[[0,0,0],[0,0],[0]],[[-214455696,-1296960,0],[-1296960,-112],[0]],[[0,0,0],[0,0],[0]],[[-201997600,-511952,0],[-511952,0],[0]],[[0,0],[0]],[[-145050528,-137760],[-137760]],[[0,0],[0]],[[-79733248,-24080],[-24080]],[[0,0],[0]],[[-33480272,-2464],[-2464]],[[0,0],[0]],[[-10641680,-112],[-112]],[[0,0],[0]],[[-2513952,0],[0]],[[0]],[[-427392]],[[0]],[[-49392]],[[0]],[[-3472]],[[0]],[[-112]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
