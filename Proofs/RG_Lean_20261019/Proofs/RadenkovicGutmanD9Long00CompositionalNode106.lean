/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode095
import Proofs.RadenkovicGutmanD9Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-648,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5832,-5832,0],[-5832,-5616,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-153576,-66096,0],[-66096,-19080,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1516320,-320760,0],[-320760,-32976,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-8171496,-883440,0],[-883440,-31968,0],[0,0]],[[0,0,0],[0,0],[0]],[[-27925848,-1544472,0],[-1544472,-18000],[0]],[[0,0,0],[0,0],[0]],[[-65482416,-1812960,0],[-1812960,-5832],[0]],[[0,0,0],[0,0],[0]],[[-110410848,-1470672,0],[-1470672,-1008],[0]],[[0,0,0],[0,0],[0]],[[-137864376,-833760,0],[-833760,-72],[0]],[[0,0,0],[0,0],[0]],[[-129855600,-329112,0],[-329112,0],[0]],[[0,0],[0]],[[-93246768,-88560],[-88560]],[[0,0],[0]],[[-51257088,-15480],[-15480]],[[0,0],[0]],[[-21523032,-1584],[-1584]],[[0,0],[0]],[[-6841080,-72],[-72]],[[0,0],[0]],[[-1616112,0],[0]],[[0]],[[-274752]],[[0]],[[-31752]],[[0]],[[-2232]],[[0]],[[-72]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
