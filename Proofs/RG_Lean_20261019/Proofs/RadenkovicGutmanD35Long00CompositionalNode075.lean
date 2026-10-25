/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode033
import Proofs.RadenkovicGutmanD35Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1225]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,22050],[0,22050]],[[0,0,0],[0,0,0],[0,0]],[[-99225,0,99225],[0,396900,58800],[99225,58800]],[[0,0,0],[0,0,0],[0,0]],[[-1719900,1786050,529200],[1786050,2116800,53900],[529200,53900]],[[0,0,0],[0,0,0],[0,0]],[[-5258925,14288400,1190700],[14288400,4762800,19600],[1190700,19600]],[[0,0,0],[0,0,0],[0,0]],[[24990000,51200100,1470000],[51200100,5880000,2450],[1470000,2450]],[[0,0,0],[0,0],[0]],[[238168175,108486000,1085350],[108486000,4341400],[1085350]],[[0,0,0],[0,0],[0]],[[879187400,151152750,490000],[151152750,1960000],[490000]],[[0,0,0],[0,0],[0]],[[2008478150,145706400,132300],[145706400,529200],[132300]],[[0,0,0],[0,0],[0]],[[3198489700,99558200,19600],[99558200,78400],[19600]],[[0,0,0],[0,0],[0]],[[3741409700,48568800,1225],[48568800,4900],[1225]],[[0,0],[0]],[[3302761700,16794750],[16794750]],[[0,0],[0]],[[2230911200,4018000],[4018000]],[[0,0],[0]],[[1158997000,632100],[632100]],[[0,0],[0]],[[462156975,58800],[58800]],[[0,0],[0]],[[140120400,2450],[2450]],[[0]],[[31700550]],[[0]],[[5179300]],[[0]],[[576975]],[[0]],[[39200]],[[0]],[[1225]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
