/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode112
import Proofs.RadenkovicGutmanD5Long00CompositionalNode116
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e117 : NestedArithmetic.Expr 3 := .plus e112 e116
noncomputable def p117 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,120],[0,120,56]],[[0,0,0],[0,0,0],[0,0,0]],[[0,1080,1980],[1080,4608,1648],[1980,1648,4]],[[0,0,0],[0,0,0],[0,0]],[[33696,63072,20976],[63072,55272,3920],[20976,3920]],[[0,0,0],[0,0,0],[0,0]],[[915516,698472,79456],[698472,220928,3576],[79456,3576]],[[0,0,0],[0,0,0],[0,0]],[[9421920,3484480,153120],[3484480,446056,1392],[153120,1392]],[[0,0,0],[0,0,0],[0,0]],[[52721844,10023112,171208],[10023112,525104,216],[171208,216]],[[0,0,0],[0,0,0],[0,0]],[[187039160,18591496,117616],[18591496,382016,8],[117616,8]],[[0,0,0],[0,0],[0]],[[456994964,23599768,50564],[23599768,174448],[50564]],[[0,0,0],[0,0],[0]],[[808347072,21190976,13408],[21190976,49128],[13408]],[[0,0,0],[0,0],[0]],[[1068619296,13689536,2068],[13689536,8016],[2068]],[[0,0,0],[0,0],[0]],[[1077847704,6393128,160],[6393128,648],[160]],[[0,0,0],[0,0],[0]],[[840268368,2144240,4],[2144240,16],[4]],[[0,0],[0]],[[509844080,506200],[506200]],[[0,0],[0]],[[241210232,80800],[80800]],[[0,0],[0]],[[88681064,8080],[8080]],[[0,0],[0]],[[25103220,432],[432]],[[0,0],[0]],[[5380064,8],[8]],[[0]],[[849040]],[[0]],[[94248]],[[0]],[[6796]],[[0]],[[272]],[[0]],[[4]]]
theorem step117 : p117=NestedHorner.add p112 p116 := by decide +kernel
#print axioms step117
theorem h117 : NestedArithmetic.compile e117=p117 := StagedExprCompile.compile_plus e117 e112 e116 p112 p116 p117 rfl h112 h116 step117
#print axioms h117
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
