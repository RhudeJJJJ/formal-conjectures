/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode033
import Proofs.RadenkovicGutmanD10Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,100]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,1800],[0,1800]],[[0,0,0],[0,0,0],[0,0]],[[-8100,0,8100],[0,32400,4800],[8100,4800]],[[0,0,0],[0,0,0],[0,0]],[[-140400,145800,43200],[145800,172800,4400],[43200,4400]],[[0,0,0],[0,0,0],[0,0]],[[-429300,1166400,97200],[1166400,388800,1600],[97200,1600]],[[0,0,0],[0,0,0],[0,0]],[[2040000,4179600,120000],[4179600,480000,200],[120000,200]],[[0,0,0],[0,0],[0]],[[19442300,8856000,88600],[8856000,354400],[88600]],[[0,0,0],[0,0],[0]],[[71770400,12339000,40000],[12339000,160000],[40000]],[[0,0,0],[0,0],[0]],[[163957400,11894400,10800],[11894400,43200],[10800]],[[0,0,0],[0,0],[0]],[[261101200,8127200,1600],[8127200,6400],[1600]],[[0,0,0],[0,0],[0]],[[305421200,3964800,100],[3964800,400],[100]],[[0,0],[0]],[[269613200,1371000],[1371000]],[[0,0],[0]],[[182115200,328000],[328000]],[[0,0],[0]],[[94612000,51600],[51600]],[[0,0],[0]],[[37727100,4800],[4800]],[[0,0],[0]],[[11438400,200],[200]],[[0]],[[2587800]],[[0]],[[422800]],[[0]],[[47100]],[[0]],[[3200]],[[0]],[[100]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
