/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode033
import Proofs.RadenkovicGutmanD31Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,961]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,17298],[0,17298]],[[0,0,0],[0,0,0],[0,0]],[[-77841,0,77841],[0,311364,46128],[77841,46128]],[[0,0,0],[0,0,0],[0,0]],[[-1349244,1401138,415152],[1401138,1660608,42284],[415152,42284]],[[0,0,0],[0,0,0],[0,0]],[[-4125573,11209104,934092],[11209104,3736368,15376],[934092,15376]],[[0,0,0],[0,0,0],[0,0]],[[19604400,40165956,1153200],[40165956,4612800,1922],[1153200,1922]],[[0,0,0],[0,0],[0]],[[186840503,85106160,851446],[85106160,3405784],[851446]],[[0,0,0],[0,0],[0]],[[689713544,118577790,384400],[118577790,1537600],[384400]],[[0,0,0],[0,0],[0]],[[1575630614,114305184,103788],[114305184,415152],[103788]],[[0,0,0],[0,0],[0]],[[2509182532,78102392,15376],[78102392,61504],[15376]],[[0,0,0],[0,0],[0]],[[2935097732,38101728,961],[38101728,3844],[961]],[[0,0],[0]],[[2590982852,13175310],[13175310]],[[0,0],[0]],[[1750127072,3152080],[3152080]],[[0,0],[0]],[[909221320,495876],[495876]],[[0,0],[0]],[[362557431,46128],[46128]],[[0,0],[0]],[[109923024,1922],[1922]],[[0]],[[24868758]],[[0]],[[4063108]],[[0]],[[452631]],[[0]],[[30752]],[[0]],[[961]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
