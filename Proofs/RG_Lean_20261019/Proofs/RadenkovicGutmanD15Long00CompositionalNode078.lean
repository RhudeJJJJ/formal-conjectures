/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode075
import Proofs.RadenkovicGutmanD15Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,225]],[[0,0],[0,0,0],[0,0]],[[0,0,2025],[0,4050,4050],[2025,4050]],[[0,0,0],[0,0,0],[0,0]],[[-18225,66825,35775],[66825,108000,10800],[35775,10800]],[[0,0,0],[0,0,0],[0,0]],[[230850,1075275,156825],[1075275,508050,9900],[156825,9900]],[[0,0,0],[0,0,0],[0,0]],[[6506325,6194475,321750],[6194475,1080900,3600],[321750,3600]],[[0,0,0],[0,0,0],[0,0]],[[50140350,19067850,369900],[19067850,1279800,450],[369900,450]],[[0,0,0],[0,0],[0]],[[208628775,36513675,255600],[36513675,909900],[255600]],[[0,0,0],[0,0],[0]],[[559417500,46873575,108225],[46873575,396450],[108225]],[[0,0,0],[0,0],[0]],[[1049780250,41980500,27450],[41980500,103500],[27450]],[[0,0,0],[0,0],[0]],[[1443919050,26759475,3825],[26759475,14850],[3825]],[[0,0,0],[0,0],[0]],[[1496738250,12207825,225],[12207825,900],[225]],[[0,0],[0]],[[1188868500,3954600],[3954600]],[[0,0],[0]],[[730019250,887625],[887625]],[[0,0],[0]],[[347386050,131175],[131175]],[[0,0],[0]],[[127642275,11475],[11475]],[[0,0],[0]],[[35837100,450],[450]],[[0]],[[7539750]],[[0]],[[1149750]],[[0]],[[119925]],[[0]],[[7650]],[[0]],[[225]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
