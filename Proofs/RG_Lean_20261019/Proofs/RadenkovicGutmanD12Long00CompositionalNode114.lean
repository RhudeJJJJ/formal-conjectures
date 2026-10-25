/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode035
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e114 : NestedArithmetic.Expr 3 := .pow e035 2
noncomputable def p114 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,1296],[0,2592],[1296]],[[0,0,0],[0,0],[0]],[[0,46656,11232],[46656,22464],[11232]],[[0,0,0],[0,0],[0]],[[419904,528768,38160],[528768,76320],[38160]],[[0,0,0],[0,0],[0]],[[5878656,2566080,65952],[2566080,131904],[65952]],[[0,0,0],[0,0],[0]],[[36811584,7067520,63936],[7067520,127872],[63936]],[[0,0,0],[0,0],[0]],[[137199744,12355776,36000],[12355776,72000],[36000]],[[0,0,0],[0,0],[0]],[[341553024,14503680,11664],[14503680,23328],[11664]],[[0,0,0],[0,0],[0]],[[603614592,11765376,2016],[11765376,4032],[2016]],[[0,0,0],[0,0],[0]],[[784910016,6670080,144],[6670080,288],[144]],[[0,0],[0]],[[767394432,2632896],[2632896]],[[0,0],[0]],[[571001472,708480],[708480]],[[0,0],[0]],[[324934272,123840],[123840]],[[0,0],[0]],[[141167808,12672],[12672]],[[0,0],[0]],[[46406016,576],[576]],[[0]],[[11334528]],[[0]],[[1991808]],[[0]],[[237888]],[[0]],[[17280]],[[0]],[[576]]]
theorem step114 : p114=NestedArithmetic.power p035 2 := by decide +kernel
#print axioms step114
theorem h114 : NestedArithmetic.compile e114=p114 := StagedExprCompile.compile_pow 2 e114 e035 p035 p114 rfl h035 step114
#print axioms h114
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
