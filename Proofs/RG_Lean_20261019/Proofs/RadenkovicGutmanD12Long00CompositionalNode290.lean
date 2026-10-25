/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode289
import Proofs.RadenkovicGutmanD12Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e290 : NestedArithmetic.Expr 3 := .times e289 e003
noncomputable def p290 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[576,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[17280,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[237888,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1991808,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[11334528,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[46406016,576,0],[576,0],[0]],[[0,0,0],[0,0],[0]],[[141167808,12672,0],[12672,0],[0]],[[0,0,0],[0,0],[0]],[[324934272,123840,0],[123840,0],[0]],[[0,0,0],[0,0],[0]],[[571001472,708480,0],[708480,0],[0]],[[0,0,0],[0,0],[0]],[[767394432,2632896,0],[2632896,0],[0]],[[0,0,0],[0,0],[0]],[[784910016,6670080,144],[6670080,288],[144]],[[0,0,0],[0,0],[0]],[[603614592,11765376,2016],[11765376,4032],[2016]],[[0,0,0],[0,0],[0]],[[341553024,14503680,11664],[14503680,23328],[11664]],[[0,0,0],[0,0],[0]],[[137199744,12355776,36000],[12355776,72000],[36000]],[[0,0,0],[0,0],[0]],[[36811584,7067520,63936],[7067520,127872],[63936]],[[0,0,0],[0,0],[0]],[[5878656,2566080,65952],[2566080,131904],[65952]],[[0,0,0],[0,0],[0]],[[419904,528768,38160],[528768,76320],[38160]],[[0,0,0],[0,0],[0]],[[0,46656,11232],[46656,22464],[11232]],[[0,0,0],[0,0],[0]],[[0,0,1296],[0,2592],[1296]]]
theorem step290 : p290=NestedArithmetic.mul p289 p003 := by decide +kernel
#print axioms step290
theorem h290 : NestedArithmetic.compile e290=p290 := StagedExprCompile.compile_times e290 e289 e003 p289 p003 p290 rfl h289 h003 step290
#print axioms h290
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
