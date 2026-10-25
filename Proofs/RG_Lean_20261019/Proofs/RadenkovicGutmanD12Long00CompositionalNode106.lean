/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode095
import Proofs.RadenkovicGutmanD12Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-864,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7776,-7776,0],[-7776,-7488,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-204768,-88128,0],[-88128,-25440,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2021760,-427680,0],[-427680,-43968,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-10895328,-1177920,0],[-1177920,-42624,0],[0,0]],[[0,0,0],[0,0],[0]],[[-37234464,-2059296,0],[-2059296,-24000],[0]],[[0,0,0],[0,0],[0]],[[-87309888,-2417280,0],[-2417280,-7776],[0]],[[0,0,0],[0,0],[0]],[[-147214464,-1960896,0],[-1960896,-1344],[0]],[[0,0,0],[0,0],[0]],[[-183819168,-1111680,0],[-1111680,-96],[0]],[[0,0,0],[0,0],[0]],[[-173140800,-438816,0],[-438816,0],[0]],[[0,0],[0]],[[-124329024,-118080],[-118080]],[[0,0],[0]],[[-68342784,-20640],[-20640]],[[0,0],[0]],[[-28697376,-2112],[-2112]],[[0,0],[0]],[[-9121440,-96],[-96]],[[0,0],[0]],[[-2154816,0],[0]],[[0]],[[-366336]],[[0]],[[-42336]],[[0]],[[-2976]],[[0]],[[-96]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
