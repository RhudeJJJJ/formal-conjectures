/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode100
import Proofs.RadenkovicGutmanD27Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,729]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-6561],[0,-13122,21546],[-6561,21546,54]],[[0,0,0],[0,0,0],[0,0]],[[-59049,-219429,78003],[-219429,414558,72468],[78003,72468]],[[0,0,0],[0,0,0],[0,0]],[[-2716254,550395,656829],[550395,2916810,79596],[656829,79596]],[[0,0,0],[0,0,0],[0,0]],[[-14510745,15451641,1863810],[15451641,7793874,33696],[1863810,33696]],[[0,0,0],[0,0,0],[0,0]],[[18286236,76384512,2729268],[76384512,10995588,5130],[2729268,5130]],[[0,0,0],[0,0,0],[0,0]],[[431863245,196304229,2314332],[196304229,9070380,108],[2314332,108]],[[0,0,0],[0,0],[0]],[[1958393700,315439731,1176147],[315439731,4512186],[1176147]],[[0,0,0],[0,0],[0]],[[5078834406,341106984,354078],[341106984,1336122],[354078]],[[0,0,0],[0,0],[0]],[[8890088634,256814901,58887],[256814901,219618],[58887]],[[0,0,0],[0,0],[0]],[[11217708792,136362555,4401],[136362555,16362],[4401]],[[0,0,0],[0,0],[0]],[[10548080064,50911254,54],[50911254,216],[54]],[[0,0],[0]],[[7521519330,13102155],[13102155]],[[0,0],[0]],[[4098573486,2223207],[2223207]],[[0,0],[0]],[[1706633253,226989],[226989]],[[0,0],[0]],[[538923996,11232],[11232]],[[0,0],[0]],[[126923274,108],[108]],[[0]],[[21640230]],[[0]],[[2536407]],[[0]],[[185598]],[[0]],[[6831]],[[0]],[[54]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
