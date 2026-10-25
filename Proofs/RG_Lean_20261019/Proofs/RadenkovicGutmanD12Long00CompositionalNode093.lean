/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode033
import Proofs.RadenkovicGutmanD12Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,144]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,3456],[0,3456,24]],[[0,0,0],[0,0,0],[0,0]],[[-11664,-7776,19440],[-7776,75168,11088],[19440,11088]],[[0,0,0],[0,0,0],[0,0]],[[-320760,295488,118584],[295488,451872,12096],[118584,12096]],[[0,0,0],[0,0,0],[0,0]],[[-1390608,2917296,300672],[2917296,1126368,5376],[300672,5376]],[[0,0,0],[0,0,0],[0,0]],[[3238920,11741472,414144],[11741472,1524672,960],[414144,960]],[[0,0,0],[0,0,0],[0,0]],[[47512656,27232416,339552],[27232416,1230336,48],[339552,48]],[[0,0,0],[0,0],[0]],[[198455880,41064768,170736],[41064768,610944],[170736]],[[0,0,0],[0,0],[0]],[[492700512,42614928,52224],[42614928,185568],[52224]],[[0,0,0],[0,0],[0]],[[840233424,31298976,9216],[31298976,32832],[9216]],[[0,0,0],[0,0],[0]],[[1045142016,16445856,816],[16445856,2976],[816]],[[0,0,0],[0,0],[0]],[[977726496,6165792,24],[6165792,96],[24]],[[0,0],[0]],[[699119328,1622160],[1622160]],[[0,0],[0]],[[384841344,288960],[288960]],[[0,0],[0]],[[163112784,32544],[32544]],[[0,0],[0]],[[52889544,2016],[2016]],[[0,0],[0]],[[12936096,48],[48]],[[0]],[[2328912]],[[0]],[[296304]],[[0]],[[24840]],[[0]],[[1200]],[[0]],[[24]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
