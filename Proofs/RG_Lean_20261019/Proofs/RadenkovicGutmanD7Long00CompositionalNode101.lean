/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode051
import Proofs.RadenkovicGutmanD7Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,49]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,1176],[0,1176,14]],[[0,0,0],[0,0,0],[0,0]],[[-3969,2646,6615],[2646,26712,3878],[6615,3878]],[[0,0,0],[0,0,0],[0,0]],[[-20034,179550,40824],[179550,165480,4396],[40824,4396]],[[0,0,0],[0,0,0],[0,0]],[[1004535,1499652,104832],[1499652,426748,2086],[104832,2086]],[[0,0,0],[0,0,0],[0,0]],[[12028506,5826212,146594],[5826212,599200,420],[146594,420]],[[0,0,0],[0,0,0],[0,0]],[[63980315,13424292,122542],[13424292,502600,28],[122542,28]],[[0,0,0],[0,0],[0]],[[206446954,20286322,63266],[20286322,260064],[63266]],[[0,0,0],[0,0],[0]],[[452868878,21150696,20104],[21150696,82684],[20104]],[[0,0,0],[0,0],[0]],[[715823864,15615418,3766],[15615418,15456],[3766]],[[0,0,0],[0,0],[0]],[[843231452,8249626,371],[8249626,1512],[371]],[[0,0,0],[0,0],[0]],[[755395368,3111892,14],[3111892,56],[14]],[[0,0],[0]],[[520554300,825160],[825160]],[[0,0],[0]],[[277283720,148666],[148666]],[[0,0],[0]],[[114052043,17052],[17052]],[[0,0],[0]],[[35966490,1092],[1092]],[[0,0],[0]],[[8569974,28],[28]],[[0]],[[1505000]],[[0]],[[186935]],[[0]],[[15302]],[[0]],[[721]],[[0]],[[14]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
