/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode043
import Proofs.RadenkovicGutmanD17Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,2601],[0,5202,-3060],[2601,-3060,900]],[[0,0,0],[0,0,0],[0,0]],[[0,89505,-4998],[89505,-62646,2940],[-4998,2940]],[[0,0,0],[0,0,0],[0,0]],[[623700,285795,-43295],[285795,-305290,26880],[-43295,26880]],[[0,0,0],[0,0,0],[0,0]],[[3861000,-776709,-11278],[-776709,-238286,32460],[-11278,32460]],[[0,0,0],[0,0,0],[0,0]],[[-8910,-5127000,230976],[-5127000,790932,13380],[230976,13380]],[[0,0,0],[0,0,0],[0,0]],[[-72972570,-8689637,503530],[-8689637,1989500,1800],[503530,1800]],[[0,0,0],[0,0],[0]],[[-326112226,-770849,495429],[-770849,2002398],[495429]],[[0,0,0],[0,0],[0]],[[-760067608,19498412,268166],[19498412,1086442],[268166]],[[0,0,0],[0,0],[0]],[[-1103685210,35665647,82189],[35665647,331958],[82189]],[[0,0,0],[0,0],[0]],[[-1010632040,34315961,13380],[34315961,53790],[13380]],[[0,0,0],[0,0],[0]],[[-485326436,20965488,900],[20965488,3600],[900]],[[0,0],[0]],[[80530870,8529305],[8529305]],[[0,0],[0]],[[344714474,2310109],[2310109]],[[0,0],[0]],[[308070150,400963],[400963]],[[0,0],[0]],[[167219214,40410],[40410]],[[0,0],[0]],[[62387940,1800],[1800]],[[0]],[[16426570]],[[0]],[[3016028]],[[0]],[[368724]],[[0]],[[27030]],[[0]],[[900]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
