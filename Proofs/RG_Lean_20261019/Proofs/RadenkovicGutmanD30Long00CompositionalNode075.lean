/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode033
import Proofs.RadenkovicGutmanD30Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,900]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,16200],[0,16200]],[[0,0,0],[0,0,0],[0,0]],[[-72900,0,72900],[0,291600,43200],[72900,43200]],[[0,0,0],[0,0,0],[0,0]],[[-1263600,1312200,388800],[1312200,1555200,39600],[388800,39600]],[[0,0,0],[0,0,0],[0,0]],[[-3863700,10497600,874800],[10497600,3499200,14400],[874800,14400]],[[0,0,0],[0,0,0],[0,0]],[[18360000,37616400,1080000],[37616400,4320000,1800],[1080000,1800]],[[0,0,0],[0,0],[0]],[[174980700,79704000,797400],[79704000,3189600],[797400]],[[0,0,0],[0,0],[0]],[[645933600,111051000,360000],[111051000,1440000],[360000]],[[0,0,0],[0,0],[0]],[[1475616600,107049600,97200],[107049600,388800],[97200]],[[0,0,0],[0,0],[0]],[[2349910800,73144800,14400],[73144800,57600],[14400]],[[0,0,0],[0,0],[0]],[[2748790800,35683200,900],[35683200,3600],[900]],[[0,0],[0]],[[2426518800,12339000],[12339000]],[[0,0],[0]],[[1639036800,2952000],[2952000]],[[0,0],[0]],[[851508000,464400],[464400]],[[0,0],[0]],[[339543900,43200],[43200]],[[0,0],[0]],[[102945600,1800],[1800]],[[0]],[[23290200]],[[0]],[[3805200]],[[0]],[[423900]],[[0]],[[28800]],[[0]],[[900]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
