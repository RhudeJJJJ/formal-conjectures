/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode033
import Proofs.RadenkovicGutmanD15Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,225]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,4050],[0,4050]],[[0,0,0],[0,0,0],[0,0]],[[-18225,0,18225],[0,72900,10800],[18225,10800]],[[0,0,0],[0,0,0],[0,0]],[[-315900,328050,97200],[328050,388800,9900],[97200,9900]],[[0,0,0],[0,0,0],[0,0]],[[-965925,2624400,218700],[2624400,874800,3600],[218700,3600]],[[0,0,0],[0,0,0],[0,0]],[[4590000,9404100,270000],[9404100,1080000,450],[270000,450]],[[0,0,0],[0,0],[0]],[[43745175,19926000,199350],[19926000,797400],[199350]],[[0,0,0],[0,0],[0]],[[161483400,27762750,90000],[27762750,360000],[90000]],[[0,0,0],[0,0],[0]],[[368904150,26762400,24300],[26762400,97200],[24300]],[[0,0,0],[0,0],[0]],[[587477700,18286200,3600],[18286200,14400],[3600]],[[0,0,0],[0,0],[0]],[[687197700,8920800,225],[8920800,900],[225]],[[0,0],[0]],[[606629700,3084750],[3084750]],[[0,0],[0]],[[409759200,738000],[738000]],[[0,0],[0]],[[212877000,116100],[116100]],[[0,0],[0]],[[84885975,10800],[10800]],[[0,0],[0]],[[25736400,450],[450]],[[0]],[[5822550]],[[0]],[[951300]],[[0]],[[105975]],[[0]],[[7200]],[[0]],[[225]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
