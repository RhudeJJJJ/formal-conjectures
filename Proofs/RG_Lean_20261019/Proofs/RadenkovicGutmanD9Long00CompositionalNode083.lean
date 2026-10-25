/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode070
import Proofs.RadenkovicGutmanD9Long00CompositionalNode082
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e083 : NestedArithmetic.Expr 3 := .plus e070 e082
noncomputable def p083 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,216],[0,216,232]],[[0,0,0],[0,0,0],[0,0,0]],[[0,1944,4860],[1944,12600,5328],[4860,5328,4]],[[0,0,0],[0,0,0],[0,0]],[[7128,166860,59616],[166860,178932,13296],[59616,13296]],[[0,0,0],[0,0,0],[0,0]],[[1118232,2034936,237600],[2034936,746816,12056],[237600,12056]],[[0,0,0],[0,0,0],[0,0]],[[15916932,10540332,467712],[10540332,1515348,4464],[467712,4464]],[[0,0,0],[0,0,0],[0,0]],[[102183204,30716628,526440],[30716628,1755496,600],[526440,600]],[[0,0,0],[0,0,0],[0,0]],[[389323660,56955572,360112],[56955572,1238016,8],[360112,8]],[[0,0,0],[0,0],[0]],[[991051880,71659696,152324],[71659696,540736],[152324]],[[0,0,0],[0,0],[0]],[[1797606776,63383184,39040],[63383184,143252],[39040]],[[0,0,0],[0,0],[0]],[[2415019616,40126116,5620],[40126116,21328],[5620]],[[0,0,0],[0,0],[0]],[[2461874756,18270900,368],[18270900,1444],[368]],[[0,0,0],[0,0],[0]],[[1932513672,5938876,4],[5938876,16],[4]],[[0,0],[0]],[[1177264992,1347068],[1347068]],[[0,0],[0]],[[557676120,203584],[203584]],[[0,0],[0]],[[204670740,18700],[18700]],[[0,0],[0]],[[57614680,844],[844]],[[0,0],[0]],[[12213384,8],[8]],[[0]],[[1890592]],[[0]],[[202884]],[[0]],[[13728]],[[0]],[[476]],[[0]],[[4]]]
theorem step083 : p083=NestedHorner.add p070 p082 := by decide +kernel
#print axioms step083
theorem h083 : NestedArithmetic.compile e083=p083 := StagedExprCompile.compile_plus e083 e070 e082 p070 p082 p083 rfl h070 h082 step083
#print axioms h083
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
