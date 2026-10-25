/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode095
import Proofs.RadenkovicGutmanD17Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1224,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-11016,-11016,0],[-11016,-10608,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-290088,-124848,0],[-124848,-36040,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2864160,-605880,0],[-605880,-62288,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-15435048,-1668720,0],[-1668720,-60384,0],[0,0]],[[0,0,0],[0,0],[0]],[[-52748824,-2917336,0],[-2917336,-34000],[0]],[[0,0,0],[0,0],[0]],[[-123689008,-3424480,0],[-3424480,-11016],[0]],[[0,0,0],[0,0],[0]],[[-208553824,-2777936,0],[-2777936,-1904],[0]],[[0,0,0],[0,0],[0]],[[-260410488,-1574880,0],[-1574880,-136],[0]],[[0,0,0],[0,0],[0]],[[-245282800,-621656,0],[-621656,0],[0]],[[0,0],[0]],[[-176132784,-167280],[-167280]],[[0,0],[0]],[[-96818944,-29240],[-29240]],[[0,0],[0]],[[-40654616,-2992],[-2992]],[[0,0],[0]],[[-12922040,-136],[-136]],[[0,0],[0]],[[-3052656,0],[0]],[[0]],[[-518976]],[[0]],[[-59976]],[[0]],[[-4216]],[[0]],[[-136]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
