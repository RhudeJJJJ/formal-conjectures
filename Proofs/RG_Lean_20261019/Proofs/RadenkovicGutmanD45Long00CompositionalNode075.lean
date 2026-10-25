/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode033
import Proofs.RadenkovicGutmanD45Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,2025]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,36450],[0,36450]],[[0,0,0],[0,0,0],[0,0]],[[-164025,0,164025],[0,656100,97200],[164025,97200]],[[0,0,0],[0,0,0],[0,0]],[[-2843100,2952450,874800],[2952450,3499200,89100],[874800,89100]],[[0,0,0],[0,0,0],[0,0]],[[-8693325,23619600,1968300],[23619600,7873200,32400],[1968300,32400]],[[0,0,0],[0,0,0],[0,0]],[[41310000,84636900,2430000],[84636900,9720000,4050],[2430000,4050]],[[0,0,0],[0,0],[0]],[[393706575,179334000,1794150],[179334000,7176600],[1794150]],[[0,0,0],[0,0],[0]],[[1453350600,249864750,810000],[249864750,3240000],[810000]],[[0,0,0],[0,0],[0]],[[3320137350,240861600,218700],[240861600,874800],[218700]],[[0,0,0],[0,0],[0]],[[5287299300,164575800,32400],[164575800,129600],[32400]],[[0,0,0],[0,0],[0]],[[6184779300,80287200,2025],[80287200,8100],[2025]],[[0,0],[0]],[[5459667300,27762750],[27762750]],[[0,0],[0]],[[3687832800,6642000],[6642000]],[[0,0],[0]],[[1915893000,1044900],[1044900]],[[0,0],[0]],[[763973775,97200],[97200]],[[0,0],[0]],[[231627600,4050],[4050]],[[0]],[[52402950]],[[0]],[[8561700]],[[0]],[[953775]],[[0]],[[64800]],[[0]],[[2025]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
