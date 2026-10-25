/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode075
import Proofs.RadenkovicGutmanD35Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1225]],[[0,0],[0,0,0],[0,0]],[[0,0,11025],[0,22050,22050],[11025,22050]],[[0,0,0],[0,0,0],[0,0]],[[-99225,363825,194775],[363825,588000,58800],[194775,58800]],[[0,0,0],[0,0,0],[0,0]],[[1256850,5854275,853825],[5854275,2766050,53900],[853825,53900]],[[0,0,0],[0,0,0],[0,0]],[[35423325,33725475,1751750],[33725475,5884900,19600],[1751750,19600]],[[0,0,0],[0,0,0],[0,0]],[[272986350,103813850,2013900],[103813850,6967800,2450],[2013900,2450]],[[0,0,0],[0,0],[0]],[[1135867775,198796675,1391600],[198796675,4953900],[1391600]],[[0,0,0],[0,0],[0]],[[3045717500,255200575,589225],[255200575,2158450],[589225]],[[0,0,0],[0,0],[0]],[[5715470250,228560500,149450],[228560500,563500],[149450]],[[0,0,0],[0,0],[0]],[[7861337050,145690475,20825],[145690475,80850],[20825]],[[0,0,0],[0,0],[0]],[[8148908250,66464825,1225],[66464825,4900],[1225]],[[0,0],[0]],[[6472728500,21530600],[21530600]],[[0,0],[0]],[[3974549250,4832625],[4832625]],[[0,0],[0]],[[1891324050,714175],[714175]],[[0,0],[0]],[[694941275,62475],[62475]],[[0,0],[0]],[[195113100,2450],[2450]],[[0]],[[41049750]],[[0]],[[6259750]],[[0]],[[652925]],[[0]],[[41650]],[[0]],[[1225]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
