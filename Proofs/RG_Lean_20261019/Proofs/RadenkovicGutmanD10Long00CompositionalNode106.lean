/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode095
import Proofs.RadenkovicGutmanD10Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-720,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6480,-6480,0],[-6480,-6240,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-170640,-73440,0],[-73440,-21200,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1684800,-356400,0],[-356400,-36640,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-9079440,-981600,0],[-981600,-35520,0],[0,0]],[[0,0,0],[0,0],[0]],[[-31028720,-1716080,0],[-1716080,-20000],[0]],[[0,0,0],[0,0],[0]],[[-72758240,-2014400,0],[-2014400,-6480],[0]],[[0,0,0],[0,0],[0]],[[-122678720,-1634080,0],[-1634080,-1120],[0]],[[0,0,0],[0,0],[0]],[[-153182640,-926400,0],[-926400,-80],[0]],[[0,0,0],[0,0],[0]],[[-144284000,-365680,0],[-365680,0],[0]],[[0,0],[0]],[[-103607520,-98400],[-98400]],[[0,0],[0]],[[-56952320,-17200],[-17200]],[[0,0],[0]],[[-23914480,-1760],[-1760]],[[0,0],[0]],[[-7601200,-80],[-80]],[[0,0],[0]],[[-1795680,0],[0]],[[0]],[[-305280]],[[0]],[[-35280]],[[0]],[[-2480]],[[0]],[[-80]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
