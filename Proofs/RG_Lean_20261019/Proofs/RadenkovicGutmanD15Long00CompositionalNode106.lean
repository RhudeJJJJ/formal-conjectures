/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode095
import Proofs.RadenkovicGutmanD15Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1080,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-9720,-9720,0],[-9720,-9360,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-255960,-110160,0],[-110160,-31800,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2527200,-534600,0],[-534600,-54960,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-13619160,-1472400,0],[-1472400,-53280,0],[0,0]],[[0,0,0],[0,0],[0]],[[-46543080,-2574120,0],[-2574120,-30000],[0]],[[0,0,0],[0,0],[0]],[[-109137360,-3021600,0],[-3021600,-9720],[0]],[[0,0,0],[0,0],[0]],[[-184018080,-2451120,0],[-2451120,-1680],[0]],[[0,0,0],[0,0],[0]],[[-229773960,-1389600,0],[-1389600,-120],[0]],[[0,0,0],[0,0],[0]],[[-216426000,-548520,0],[-548520,0],[0]],[[0,0],[0]],[[-155411280,-147600],[-147600]],[[0,0],[0]],[[-85428480,-25800],[-25800]],[[0,0],[0]],[[-35871720,-2640],[-2640]],[[0,0],[0]],[[-11401800,-120],[-120]],[[0,0],[0]],[[-2693520,0],[0]],[[0]],[[-457920]],[[0]],[[-52920]],[[0]],[[-3720]],[[0]],[[-120]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
