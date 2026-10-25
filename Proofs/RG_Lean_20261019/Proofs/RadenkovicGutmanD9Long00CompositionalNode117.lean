/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode112
import Proofs.RadenkovicGutmanD9Long00CompositionalNode116
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e117 : NestedArithmetic.Expr 3 := .plus e112 e116
noncomputable def p117 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,216],[0,216,232]],[[0,0,0],[0,0,0],[0,0,0]],[[0,1944,4860],[1944,8064,5328],[4860,5328,4]],[[0,0,0],[0,0,0],[0,0]],[[71280,134784,59616],[134784,139944,13296],[59616,13296]],[[0,0,0],[0,0,0],[0,0]],[[2023164,1688904,237600],[1688904,616064,12056],[237600,12056]],[[0,0,0],[0,0,0],[0,0]],[[21913200,8960832,467712],[8960832,1294056,4464],[467712,4464]],[[0,0,0],[0,0,0],[0,0]],[[127235316,26679048,526440],[26679048,1548208,600],[526440,600]],[[0,0,0],[0,0,0],[0,0]],[[463161352,50500232,360112],[50500232,1128000,8],[360112,8]],[[0,0,0],[0,0],[0]],[[1152296276,64854904,152324],[64854904,508912],[152324]],[[0,0,0],[0,0],[0]],[[2064405728,58552992,39040],[58552992,139112],[39040]],[[0,0,0],[0,0],[0]],[[2753457632,37831296,5620],[37831296,21328],[5620]],[[0,0,0],[0,0],[0]],[[2793480152,17574696,368],[17574696,1480],[368]],[[0,0,0],[0,0],[0]],[[2184732048,5825008,4],[5825008,16],[4]],[[0,0],[0]],[[1326541872,1346168],[1346168]],[[0,0],[0]],[[626364984,207040],[207040]],[[0,0],[0]],[[229115064,19312],[19312]],[[0,0],[0]],[[64267444,880],[880]],[[0,0],[0]],[[13570944,8],[8]],[[0]],[[2091472]],[[0]],[[223224]],[[0]],[[14988]],[[0]],[[512]],[[0]],[[4]]]
theorem step117 : p117=NestedHorner.add p112 p116 := by decide +kernel
#print axioms step117
theorem h117 : NestedArithmetic.compile e117=p117 := StagedExprCompile.compile_plus e117 e112 e116 p112 p116 p117 rfl h112 h116 step117
#print axioms h117
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
