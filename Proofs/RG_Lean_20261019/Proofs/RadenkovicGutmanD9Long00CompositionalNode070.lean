/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode067
import Proofs.RadenkovicGutmanD9Long00CompositionalNode069
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e070 : NestedArithmetic.Expr 3 := .plus e067 e069
noncomputable def p070 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,81]],[[0,0],[0,0,0],[0,0,0]],[[0,0,729],[0,1458,1674],[729,1674,232]],[[0,0,0],[0,0,0],[0,0,0]],[[-6561,26001,17739],[26001,51480,9216],[17739,9216,4]],[[0,0,0],[0,0,0],[0,0]],[[90234,553959,116073],[553959,361830,16860],[116073,16860]],[[0,0,0],[0,0,0],[0,0]],[[3460509,4264947,353430],[4264947,1135940,13352],[353430,13352]],[[0,0,0],[0,0,0],[0,0]],[[33967458,17404758,600876],[17404758,1976076,4626],[600876,4626]],[[0,0,0],[0,0,0],[0,0]],[[177289563,43861551,618456],[43861551,2083060,600],[618456,600]],[[0,0,0],[0,0,0],[0,0]],[[590713960,73830059,399073],[73830059,1380738,8],[399073,8]],[[0,0,0],[0,0],[0]],[[1368972770,86772676,162206],[86772676,577996],[162206]],[[0,0,0],[0,0],[0]],[[2317417634,73016595,40417],[73016595,148598],[40417]],[[0,0,0],[0,0],[0]],[[2953845386,44520933,5701],[44520933,21652],[5701]],[[0,0,0],[0,0],[0]],[[2889867416,19694556,368],[19694556,1444],[368]],[[0,0,0],[0,0],[0]],[[2195320602,6258421,4],[6258421,16],[4]],[[0,0],[0]],[[1302323970,1394291],[1394291]],[[0,0],[0]],[[603627339,207715],[207715]],[[0,0],[0]],[[217572096,18862],[18862]],[[0,0],[0]],[[60328990,844],[844]],[[0,0],[0]],[[12627294,8],[8]],[[0]],[[1933765]],[[0]],[[205638]],[[0]],[[13809]],[[0]],[[476]],[[0]],[[4]]]
theorem step070 : p070=NestedHorner.add p067 p069 := by decide +kernel
#print axioms step070
theorem h070 : NestedArithmetic.compile e070=p070 := StagedExprCompile.compile_plus e070 e067 e069 p067 p069 p070 rfl h067 h069 step070
#print axioms h070
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
