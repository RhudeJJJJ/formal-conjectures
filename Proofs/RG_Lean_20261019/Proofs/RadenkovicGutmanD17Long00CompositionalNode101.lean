/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode051
import Proofs.RadenkovicGutmanD17Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,289]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,6936],[0,6936,34]],[[0,0,0],[0,0,0],[0,0]],[[-23409,15606,39015],[15606,156672,21998],[39015,21998]],[[0,0,0],[0,0,0],[0,0]],[[-122094,1051110,236844],[1051110,952680,23596],[236844,23596]],[[0,0,0],[0,0,0],[0,0]],[[5785695,8684892,597312],[8684892,2407268,10166],[597312,10166]],[[0,0,0],[0,0,0],[0,0]],[[69106326,33363452,817394],[33363452,3300720,1700],[817394,1700]],[[0,0,0],[0,0,0],[0,0]],[[365337395,75953892,664462],[75953892,2688040,68],[664462,68]],[[0,0,0],[0,0],[0]],[[1170494574,113262602,330106],[113262602,1337424],[330106]],[[0,0,0],[0,0],[0]],[[2547792958,116306656,99144],[116306656,402084],[99144]],[[0,0,0],[0,0],[0]],[[3993296464,84337578,16966],[84337578,68816],[16966]],[[0,0,0],[0,0],[0]],[[4660516612,43583546,1411],[43583546,5712],[1411]],[[0,0,0],[0,0],[0]],[[4131741608,15984012,34],[15984012,136],[34]],[[0,0],[0]],[[2813443900,4081360],[4081360]],[[0,0],[0]],[[1477795720,696626],[696626]],[[0,0],[0]],[[597680883,73372],[73372]],[[0,0],[0]],[[184574270,4012],[4012]],[[0,0],[0]],[[42809094,68],[68]],[[0]],[[7248800]],[[0]],[[854335]],[[0]],[[64362]],[[0]],[[2601]],[[0]],[[34]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
