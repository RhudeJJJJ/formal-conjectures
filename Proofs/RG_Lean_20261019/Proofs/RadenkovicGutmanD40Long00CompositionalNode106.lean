/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode095
import Proofs.RadenkovicGutmanD40Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2880,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-25920,-25920,0],[-25920,-24960,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-682560,-293760,0],[-293760,-84800,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6739200,-1425600,0],[-1425600,-146560,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-36317760,-3926400,0],[-3926400,-142080,0],[0,0]],[[0,0,0],[0,0],[0]],[[-124114880,-6864320,0],[-6864320,-80000],[0]],[[0,0,0],[0,0],[0]],[[-291032960,-8057600,0],[-8057600,-25920],[0]],[[0,0,0],[0,0],[0]],[[-490714880,-6536320,0],[-6536320,-4480],[0]],[[0,0,0],[0,0],[0]],[[-612730560,-3705600,0],[-3705600,-320],[0]],[[0,0,0],[0,0],[0]],[[-577136000,-1462720,0],[-1462720,0],[0]],[[0,0],[0]],[[-414430080,-393600],[-393600]],[[0,0],[0]],[[-227809280,-68800],[-68800]],[[0,0],[0]],[[-95657920,-7040],[-7040]],[[0,0],[0]],[[-30404800,-320],[-320]],[[0,0],[0]],[[-7182720,0],[0]],[[0]],[[-1221120]],[[0]],[[-141120]],[[0]],[[-9920]],[[0]],[[-320]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
