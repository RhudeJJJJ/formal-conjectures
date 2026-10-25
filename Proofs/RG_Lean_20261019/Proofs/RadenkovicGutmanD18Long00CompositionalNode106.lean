/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode095
import Proofs.RadenkovicGutmanD18Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1296,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-11664,-11664,0],[-11664,-11232,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-307152,-132192,0],[-132192,-38160,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3032640,-641520,0],[-641520,-65952,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-16342992,-1766880,0],[-1766880,-63936,0],[0,0]],[[0,0,0],[0,0],[0]],[[-55851696,-3088944,0],[-3088944,-36000],[0]],[[0,0,0],[0,0],[0]],[[-130964832,-3625920,0],[-3625920,-11664],[0]],[[0,0,0],[0,0],[0]],[[-220821696,-2941344,0],[-2941344,-2016],[0]],[[0,0,0],[0,0],[0]],[[-275728752,-1667520,0],[-1667520,-144],[0]],[[0,0,0],[0,0],[0]],[[-259711200,-658224,0],[-658224,0],[0]],[[0,0],[0]],[[-186493536,-177120],[-177120]],[[0,0],[0]],[[-102514176,-30960],[-30960]],[[0,0],[0]],[[-43046064,-3168],[-3168]],[[0,0],[0]],[[-13682160,-144],[-144]],[[0,0],[0]],[[-3232224,0],[0]],[[0]],[[-549504]],[[0]],[[-63504]],[[0]],[[-4464]],[[0]],[[-144]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
