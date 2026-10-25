/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode095
import Proofs.RadenkovicGutmanD20Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1440,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-12960,-12960,0],[-12960,-12480,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-341280,-146880,0],[-146880,-42400,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3369600,-712800,0],[-712800,-73280,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-18158880,-1963200,0],[-1963200,-71040,0],[0,0]],[[0,0,0],[0,0],[0]],[[-62057440,-3432160,0],[-3432160,-40000],[0]],[[0,0,0],[0,0],[0]],[[-145516480,-4028800,0],[-4028800,-12960],[0]],[[0,0,0],[0,0],[0]],[[-245357440,-3268160,0],[-3268160,-2240],[0]],[[0,0,0],[0,0],[0]],[[-306365280,-1852800,0],[-1852800,-160],[0]],[[0,0,0],[0,0],[0]],[[-288568000,-731360,0],[-731360,0],[0]],[[0,0],[0]],[[-207215040,-196800],[-196800]],[[0,0],[0]],[[-113904640,-34400],[-34400]],[[0,0],[0]],[[-47828960,-3520],[-3520]],[[0,0],[0]],[[-15202400,-160],[-160]],[[0,0],[0]],[[-3591360,0],[0]],[[0]],[[-610560]],[[0]],[[-70560]],[[0]],[[-4960]],[[0]],[[-160]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
