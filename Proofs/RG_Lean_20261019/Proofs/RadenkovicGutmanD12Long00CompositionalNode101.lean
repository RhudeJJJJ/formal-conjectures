/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode051
import Proofs.RadenkovicGutmanD12Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,144]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,3456],[0,3456,24]],[[0,0,0],[0,0,0],[0,0]],[[-11664,7776,19440],[7776,78192,11088],[19440,11088]],[[0,0,0],[0,0,0],[0,0]],[[-60264,524880,118584],[524880,478080,12096],[118584,12096]],[[0,0,0],[0,0,0],[0,0]],[[2903040,4350672,300672],[4350672,1215408,5376],[300672,5376]],[[0,0,0],[0,0,0],[0,0]],[[34700616,16769232,414144],[16769232,1678560,960],[414144,960]],[[0,0,0],[0,0,0],[0,0]],[[183782880,38313792,339552],[38313792,1379520,48],[339552,48]],[[0,0,0],[0,0],[0]],[[590070264,57363312,170736],[57363312,694944],[170736]],[[0,0,0],[0,0],[0]],[[1287394368,59178576,52224],[59178576,212784],[52224]],[[0,0,0],[0,0],[0]],[[2022962064,43150848,9216],[43150848,37536],[9216]],[[0,0,0],[0,0],[0]],[[2367658032,22453536,816],[22453536,3312],[816]],[[0,0,0],[0,0],[0]],[[2105743488,8308752,24],[8308752,96],[24]],[[0,0],[0]],[[1439169600,2147760],[2147760]],[[0,0],[0]],[[759246720,373296],[373296]],[[0,0],[0]],[[308705088,40512],[40512]],[[0,0],[0]],[[95972280,2352],[2352]],[[0,0],[0]],[[22454784,48],[48]],[[0]],[[3848400]],[[0]],[[461760]],[[0]],[[35832]],[[0]],[[1536]],[[0]],[[24]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
