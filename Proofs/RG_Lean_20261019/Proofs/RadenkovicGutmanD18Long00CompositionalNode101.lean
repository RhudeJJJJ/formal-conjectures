/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode051
import Proofs.RadenkovicGutmanD18Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,324]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,7776],[0,7776,36]],[[0,0,0],[0,0,0],[0,0]],[[-26244,17496,43740],[17496,175608,24624],[43740,24624]],[[0,0,0],[0,0,0],[0,0]],[[-137052,1178064,265356],[1178064,1067040,26352],[265356,26352]],[[0,0,0],[0,0,0],[0,0]],[[6480324,9729720,668736],[9729720,2694024,11304],[668736,11304]],[[0,0,0],[0,0,0],[0,0]],[[77395500,37360440,914328],[37360440,3690288,1872],[914328,1872]],[[0,0,0],[0,0,0],[0,0]],[[409058532,85011984,742392],[85011984,3001536,72],[742392,72]],[[0,0,0],[0,0],[0]],[[1310195556,126701136,368208],[126701136,1490832],[368208]],[[0,0,0],[0,0],[0]],[[2850977448,130024296,110304],[130024296,447048],[110304]],[[0,0,0],[0,0],[0]],[[4466946888,94213080,18792],[94213080,76176],[18792]],[[0,0,0],[0,0],[0]],[[5211300168,48640680,1548],[48640680,6264],[1548]],[[0,0,0],[0,0],[0]],[[4618019232,17816472,36],[17816472,144],[36]],[[0,0],[0]],[[3142977840,4541400],[4541400]],[[0,0],[0]],[[1649895840,773136],[773136]],[[0,0],[0]],[[666794772,81072],[81072]],[[0,0],[0]],[[205726212,4392],[4392]],[[0,0],[0]],[[47656296,72],[72]],[[0]],[[8055720]],[[0]],[[946980]],[[0]],[[71028]],[[0]],[[2844]],[[0]],[[36]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
