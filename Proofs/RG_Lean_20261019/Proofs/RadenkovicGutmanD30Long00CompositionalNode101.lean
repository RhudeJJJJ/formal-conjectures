/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode051
import Proofs.RadenkovicGutmanD30Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,900]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,21600],[0,21600,60]],[[0,0,0],[0,0,0],[0,0]],[[-72900,48600,121500],[48600,487080,67680],[121500,67680]],[[0,0,0],[0,0,0],[0,0]],[[-383940,3265920,733860],[3265920,2944800,71280],[733860,71280]],[[0,0,0],[0,0,0],[0,0]],[[17886420,26895240,1840320],[26895240,7393080,29640],[1840320,29640]],[[0,0,0],[0,0,0],[0,0]],[[213474420,102956040,2500920],[102956040,10058640,4560],[2500920,4560]],[[0,0,0],[0,0,0],[0,0]],[[1126378260,233490960,2014200],[233490960,8110080,120],[2014200,120]],[[0,0,0],[0,0],[0]],[[3600626460,346689120,987360],[346689120,3979440],[987360]],[[0,0,0],[0,0],[0]],[[7817915400,354228600,290400],[354228600,1171320],[290400]],[[0,0,0],[0,0],[0]],[[12219924120,255311160,47880],[255311160,193200],[47880]],[[0,0,0],[0,0],[0]],[[14218210680,130935720,3660],[130935720,14760],[3660]],[[0,0,0],[0,0],[0]],[[12561378720,47538600,60],[47538600,240],[60]],[[0,0],[0]],[[8519041200,11968200],[11968200]],[[0,0],[0]],[[4453245600,1999200],[1999200]],[[0,0],[0]],[[1790448420,202800],[202800]],[[0,0],[0]],[[548769660,10200],[10200]],[[0,0],[0]],[[126007560,120],[120]],[[0]],[[21036600]],[[0]],[[2426100]],[[0]],[[175980]],[[0]],[[6540]],[[0]],[[60]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
