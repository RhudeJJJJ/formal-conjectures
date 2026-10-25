/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode075
import Proofs.RadenkovicGutmanD45Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,2025]],[[0,0],[0,0,0],[0,0]],[[0,0,18225],[0,36450,36450],[18225,36450]],[[0,0,0],[0,0,0],[0,0]],[[-164025,601425,321975],[601425,972000,97200],[321975,97200]],[[0,0,0],[0,0,0],[0,0]],[[2077650,9677475,1411425],[9677475,4572450,89100],[1411425,89100]],[[0,0,0],[0,0,0],[0,0]],[[58556925,55750275,2895750],[55750275,9728100,32400],[2895750,32400]],[[0,0,0],[0,0,0],[0,0]],[[451263150,171610650,3329100],[171610650,11518200,4050],[3329100,4050]],[[0,0,0],[0,0],[0]],[[1877658975,328623075,2300400],[328623075,8189100],[2300400]],[[0,0,0],[0,0],[0]],[[5034757500,421862175,974025],[421862175,3568050],[974025]],[[0,0,0],[0,0],[0]],[[9448022250,377824500,247050],[377824500,931500],[247050]],[[0,0,0],[0,0],[0]],[[12995271450,240835275,34425],[240835275,133650],[34425]],[[0,0,0],[0,0],[0]],[[13470644250,109870425,2025],[109870425,8100],[2025]],[[0,0],[0]],[[10699816500,35591400],[35591400]],[[0,0],[0]],[[6570173250,7988625],[7988625]],[[0,0],[0]],[[3126474450,1180575],[1180575]],[[0,0],[0]],[[1148780475,103275],[103275]],[[0,0],[0]],[[322533900,4050],[4050]],[[0]],[[67857750]],[[0]],[[10347750]],[[0]],[[1079325]],[[0]],[[68850]],[[0]],[[2025]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
