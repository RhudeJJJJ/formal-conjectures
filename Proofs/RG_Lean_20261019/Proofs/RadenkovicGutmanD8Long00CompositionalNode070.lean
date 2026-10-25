/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode067
import Proofs.RadenkovicGutmanD8Long00CompositionalNode069
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e070 : NestedArithmetic.Expr 3 := .plus e067 e069
noncomputable def p070 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,64]],[[0,0],[0,0,0],[0,0,0]],[[0,0,576],[0,1152,1344],[576,1344,176]],[[0,0,0],[0,0,0],[0,0,0]],[[-5184,20736,14208],[20736,41376,7264],[14208,7264,4]],[[0,0,0],[0,0,0],[0,0]],[[74736,444960,92656],[444960,289064,13192],[92656,13192]],[[0,0,0],[0,0,0],[0,0]],[[2816964,3423816,281220],[3423816,903264,10432],[281220,10432]],[[0,0,0],[0,0,0],[0,0]],[[27553704,13949976,477120],[13949976,1566824,3632],[477120,3632]],[[0,0,0],[0,0,0],[0,0]],[[143498348,35104984,490608],[35104984,1649488,480],[490608,480]],[[0,0,0],[0,0,0],[0,0]],[[477351672,59030240,316640],[59030240,1093536,8],[316640,8]],[[0,0,0],[0,0],[0]],[[1104918356,69339480,128920],[69339480,458640],[128920]],[[0,0,0],[0,0],[0]],[[1868779952,58342936,32256],[58342936,118440],[32256]],[[0,0,0],[0,0],[0]],[[2380607320,35590992,4592],[35590992,17424],[4592]],[[0,0,0],[0,0],[0]],[[2328335528,15762592,304],[15762592,1192],[304]],[[0,0,0],[0,0],[0]],[[1768714816,5019480,4],[5019480,16],[4]],[[0,0],[0]],[[1049563136,1122248],[1122248]],[[0,0],[0]],[[486800288,168216],[168216]],[[0,0],[0]],[[175664392,15456],[15456]],[[0,0],[0]],[[48796148,712],[712]],[[0,0],[0]],[[10241424,8],[8]],[[0]],[[1575096]],[[0]],[[168680]],[[0]],[[11476]],[[0]],[[408]],[[0]],[[4]]]
theorem step070 : p070=NestedHorner.add p067 p069 := by decide +kernel
#print axioms step070
theorem h070 : NestedArithmetic.compile e070=p070 := StagedExprCompile.compile_plus e070 e067 e069 p067 p069 p070 rfl h067 h069 step070
#print axioms h070
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
