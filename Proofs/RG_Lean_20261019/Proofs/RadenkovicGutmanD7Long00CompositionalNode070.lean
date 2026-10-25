/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode067
import Proofs.RadenkovicGutmanD7Long00CompositionalNode069
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e070 : NestedArithmetic.Expr 3 := .plus e067 e069
noncomputable def p070 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,49]],[[0,0],[0,0,0],[0,0,0]],[[0,0,441],[0,882,1050],[441,1050,128]],[[0,0,0],[0,0,0],[0,0,0]],[[-3969,16065,11067],[16065,32376,5552],[11067,5552,4]],[[0,0,0],[0,0,0],[0,0]],[[60642,347895,71905],[347895,224654,9996],[71905,9996]],[[0,0,0],[0,0,0],[0,0]],[[2239461,2675979,217446],[2675979,698260,7896],[217446,7896]],[[0,0,0],[0,0,0],[0,0]],[[21816978,10884934,368092],[10884934,1207380,2770],[368092,2770]],[[0,0,0],[0,0,0],[0,0]],[[113344379,27350951,378184],[27350951,1269508,376],[378184,376]],[[0,0,0],[0,0,0],[0,0]],[[376379896,45945339,244257],[45945339,842210,8],[244257,8]],[[0,0,0],[0,0],[0]],[[870085722,53946060,99726],[53946060,354300],[99726]],[[0,0,0],[0,0],[0]],[[1470302626,45399779,25105],[45399779,92094],[25105]],[[0,0,0],[0,0],[0]],[[1872012938,27721013,3621],[27721013,13732],[3621]],[[0,0,0],[0,0],[0]],[[1830588720,12299836,248],[12299836,972],[248]],[[0,0,0],[0,0],[0]],[[1390868970,3929037,4],[3929037,16],[4]],[[0,0],[0]],[[825846418,882931],[882931]],[[0,0],[0]],[[383459339,133483],[133483]],[[0,0],[0]],[[138613632,12462],[12462]],[[0,0],[0]],[[38604534,596],[596]],[[0,0],[0]],[[8133854,8],[8]],[[0]],[[1258373]],[[0]],[[136054]],[[0]],[[9417]],[[0]],[[348]],[[0]],[[4]]]
theorem step070 : p070=NestedHorner.add p067 p069 := by decide +kernel
#print axioms step070
theorem h070 : NestedArithmetic.compile e070=p070 := StagedExprCompile.compile_plus e070 e067 e069 p067 p069 p070 rfl h067 h069 step070
#print axioms h070
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
