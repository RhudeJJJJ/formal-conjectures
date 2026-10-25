/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode095
import Proofs.RadenkovicGutmanD23Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1656,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-14904,-14904,0],[-14904,-14352,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-392472,-168912,0],[-168912,-48760,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3875040,-819720,0],[-819720,-84272,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-20882712,-2257680,0],[-2257680,-81696,0],[0,0]],[[0,0,0],[0,0],[0]],[[-71366056,-3946984,0],[-3946984,-46000],[0]],[[0,0,0],[0,0],[0]],[[-167343952,-4633120,0],[-4633120,-14904],[0]],[[0,0,0],[0,0],[0]],[[-282161056,-3758384,0],[-3758384,-2576],[0]],[[0,0,0],[0,0],[0]],[[-352320072,-2130720,0],[-2130720,-184],[0]],[[0,0,0],[0,0],[0]],[[-331853200,-841064,0],[-841064,0],[0]],[[0,0],[0]],[[-238297296,-226320],[-226320]],[[0,0],[0]],[[-130990336,-39560],[-39560]],[[0,0],[0]],[[-55003304,-4048],[-4048]],[[0,0],[0]],[[-17482760,-184],[-184]],[[0,0],[0]],[[-4130064,0],[0]],[[0]],[[-702144]],[[0]],[[-81144]],[[0]],[[-5704]],[[0]],[[-184]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
