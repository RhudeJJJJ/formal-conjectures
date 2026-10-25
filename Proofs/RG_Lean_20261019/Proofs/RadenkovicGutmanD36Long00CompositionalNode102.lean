/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode100
import Proofs.RadenkovicGutmanD36Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1296]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-11664],[0,-23328,38448],[-11664,38448,72]],[[0,0,0],[0,0,0],[0,0]],[[-104976,-388800,139968],[-388800,741312,129024],[139968,129024]],[[0,0,0],[0,0,0],[0,0]],[[-4811400,1022544,1174824],[1022544,5206464,141120],[1174824,141120]],[[0,0,0],[0,0,0],[0,0]],[[-25392528,27778464,3328128],[27778464,13889088,59184],[3328128,59184]],[[0,0,0],[0,0,0],[0,0]],[[35732664,136796544,4865040],[136796544,19555776,8784],[4865040,8784]],[[0,0,0],[0,0,0],[0,0]],[[781346736,350799120,4116096],[350799120,16089408,144],[4116096,144]],[[0,0,0],[0,0],[0]],[[3516927768,562670352,2084976],[562670352,7973856],[2084976]],[[0,0,0],[0,0],[0]],[[9089573472,607347216,624384],[607347216,2347200],[624384]],[[0,0,0],[0,0],[0]],[[15873707664,456346368,102816],[456346368,381600],[102816]],[[0,0,0],[0,0],[0]],[[19991656224,241733088,7488],[241733088,27648],[7488]],[[0,0,0],[0,0],[0]],[[18765305280,89979120,72],[89979120,288],[72]],[[0,0],[0]],[[13357562400,23060160],[23060160]],[[0,0],[0]],[[7265156832,3888000],[3888000]],[[0,0],[0]],[[3018830832,392400],[392400]],[[0,0],[0]],[[950892120,18864],[18864]],[[0,0],[0]],[[223225632,144],[144]],[[0]],[[37890000]],[[0]],[[4410576]],[[0]],[[318744]],[[0]],[[11376]],[[0]],[[72]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
