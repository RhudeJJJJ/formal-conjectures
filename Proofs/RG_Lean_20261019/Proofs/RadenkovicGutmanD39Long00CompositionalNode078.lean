/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode075
import Proofs.RadenkovicGutmanD39Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1521]],[[0,0],[0,0,0],[0,0]],[[0,0,13689],[0,27378,27378],[13689,27378]],[[0,0,0],[0,0,0],[0,0]],[[-123201,451737,241839],[451737,730080,73008],[241839,73008]],[[0,0,0],[0,0,0],[0,0]],[[1560546,7268859,1060137],[7268859,3434418,66924],[1060137,66924]],[[0,0,0],[0,0,0],[0,0]],[[43982757,41874651,2175030],[41874651,7306884,24336],[2175030,24336]],[[0,0,0],[0,0,0],[0,0]],[[338948766,128898666,2500524],[128898666,8651448,3042],[2500524,3042]],[[0,0,0],[0,0],[0]],[[1410330519,246832443,1727856],[246832443,6150924],[1727856]],[[0,0,0],[0,0],[0]],[[3781662300,316865367,731601],[316865367,2680002],[731601]],[[0,0,0],[0,0],[0]],[[7096514490,283788180,185562],[283788180,699660],[185562]],[[0,0,0],[0,0],[0]],[[9760892778,180894051,25857],[180894051,100386],[25857]],[[0,0,0],[0,0],[0]],[[10117950570,82524897,1521],[82524897,6084],[1521]],[[0,0],[0]],[[8036751060,26733096],[26733096]],[[0,0],[0]],[[4934930130,6000345],[6000345]],[[0,0],[0]],[[2348329698,886743],[886743]],[[0,0],[0]],[[862861779,77571],[77571]],[[0,0],[0]],[[242258796,3042],[3042]],[[0]],[[50968710]],[[0]],[[7772310]],[[0]],[[810693]],[[0]],[[51714]],[[0]],[[1521]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
