/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode035
import Proofs.RadenkovicGutmanD32Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-9216],[0,-18432,5760],[-9216,5760]],[[0,0,0],[0,0,0],[0,0]],[[0,-252288,-28032],[-252288,47616,24960],[-28032,24960]],[[0,0,0],[0,0,0],[0,0]],[[-1555200,-1327104,91520],[-1327104,908800,30720],[91520,30720]],[[0,0,0],[0,0,0],[0,0]],[[-10990080,1032192,533248],[1032192,3070976,13440],[533248,13440]],[[0,0,0],[0,0,0],[0,0]],[[-1603584,24398080,998784],[24398080,4904448,1920],[998784,1920]],[[0,0,0],[0,0],[0]],[[248587776,84301568,965120],[84301568,4372480],[965120]],[[0,0,0],[0,0],[0]],[[1278541056,155958272,529536],[155958272,2284032],[529536]],[[0,0,0],[0,0],[0]],[[3504029696,183278336,166144],[183278336,693248],[166144]],[[0,0,0],[0,0],[0]],[[6329035776,145521024,27776],[145521024,113152],[27776]],[[0,0,0],[0,0],[0]],[[8137541888,79959424,1920],[79959424,7680],[1920]],[[0,0],[0]],[[7734359808,30464896],[30464896]],[[0,0],[0]],[[5542807808,7901440],[7901440]],[[0,0],[0]],[[3022010368,1331072],[1331072]],[[0,0],[0]],[[1254227968,131328],[131328]],[[0,0],[0]],[[393268992,5760],[5760]],[[0]],[[91556352]],[[0]],[[15332352]],[[0]],[[1745152]],[[0]],[[120832]],[[0]],[[3840]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
