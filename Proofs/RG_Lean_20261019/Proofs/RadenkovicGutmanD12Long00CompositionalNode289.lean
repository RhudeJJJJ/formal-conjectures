/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode217
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e289 : NestedArithmetic.Expr 3 := .pow e217 2
noncomputable def p289 : NestedHorner.Poly 3 := [[[576],[0],[0]],[[0,0],[0,0],[0]],[[17280,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[237888,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1991808,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[11334528,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[46406016,576,0],[576,0],[0]],[[0,0,0],[0,0],[0]],[[141167808,12672,0],[12672,0],[0]],[[0,0,0],[0,0],[0]],[[324934272,123840,0],[123840,0],[0]],[[0,0,0],[0,0],[0]],[[571001472,708480,0],[708480,0],[0]],[[0,0,0],[0,0],[0]],[[767394432,2632896,0],[2632896,0],[0]],[[0,0,0],[0,0],[0]],[[784910016,6670080,144],[6670080,288],[144]],[[0,0,0],[0,0],[0]],[[603614592,11765376,2016],[11765376,4032],[2016]],[[0,0,0],[0,0],[0]],[[341553024,14503680,11664],[14503680,23328],[11664]],[[0,0,0],[0,0],[0]],[[137199744,12355776,36000],[12355776,72000],[36000]],[[0,0,0],[0,0],[0]],[[36811584,7067520,63936],[7067520,127872],[63936]],[[0,0,0],[0,0],[0]],[[5878656,2566080,65952],[2566080,131904],[65952]],[[0,0,0],[0,0],[0]],[[419904,528768,38160],[528768,76320],[38160]],[[0,0,0],[0,0],[0]],[[0,46656,11232],[46656,22464],[11232]],[[0,0,0],[0,0],[0]],[[0,0,1296],[0,2592],[1296]]]
theorem step289 : p289=NestedArithmetic.power p217 2 := by decide +kernel
#print axioms step289
theorem h289 : NestedArithmetic.compile e289=p289 := StagedExprCompile.compile_pow 2 e289 e217 p217 p289 rfl h217 step289
#print axioms h289
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
