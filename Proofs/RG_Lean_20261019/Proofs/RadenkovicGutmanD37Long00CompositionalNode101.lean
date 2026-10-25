/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode051
import Proofs.RadenkovicGutmanD37Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1369]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,32856],[0,32856,74]],[[0,0,0],[0,0,0],[0,0]],[[-110889,73926,184815],[73926,740592,102638],[184815,102638]],[[0,0,0],[0,0,0],[0,0]],[[-585414,4965030,1114884],[4965030,4471080,107596],[1114884,107596]],[[0,0,0],[0,0,0],[0,0]],[[27157815,40853772,2791872],[40853772,11206708,44326],[2791872,44326]],[[0,0,0],[0,0,0],[0,0]],[[324065166,156252332,3787394],[156252332,15217360,6660],[3787394,6660]],[[0,0,0],[0,0,0],[0,0]],[[1709074955,354020292,3043102],[354020292,12238120,148],[3043102,148]],[[0,0,0],[0,0],[0]],[[5460201814,525082762,1486586],[525082762,5983344],[1486586]],[[0,0,0],[0,0],[0]],[[11848118318,535820976,434824],[535820976,1751284],[434824]],[[0,0,0],[0,0],[0]],[[18506596064,385597498,70966],[385597498,285936],[70966]],[[0,0,0],[0,0],[0]],[[21516270932,197364586,5291],[197364586,21312],[5291]],[[0,0,0],[0,0],[0]],[[18992234088,71469052,74],[71469052,296],[74]],[[0,0],[0]],[[12867131100,17925760],[17925760]],[[0,0],[0]],[[6717851720,2976946],[2976946]],[[0,0],[0]],[[2696811563,298812],[298812]],[[0,0],[0]],[[824944230,14652],[14652]],[[0,0],[0]],[[188921334,148],[148]],[[0]],[[31420400]],[[0]],[[3602135]],[[0]],[[258482]],[[0]],[[9361]],[[0]],[[74]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
