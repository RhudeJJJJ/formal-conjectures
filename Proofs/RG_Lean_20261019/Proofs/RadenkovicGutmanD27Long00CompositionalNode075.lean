/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode033
import Proofs.RadenkovicGutmanD27Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,729]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,13122],[0,13122]],[[0,0,0],[0,0,0],[0,0]],[[-59049,0,59049],[0,236196,34992],[59049,34992]],[[0,0,0],[0,0,0],[0,0]],[[-1023516,1062882,314928],[1062882,1259712,32076],[314928,32076]],[[0,0,0],[0,0,0],[0,0]],[[-3129597,8503056,708588],[8503056,2834352,11664],[708588,11664]],[[0,0,0],[0,0,0],[0,0]],[[14871600,30469284,874800],[30469284,3499200,1458],[874800,1458]],[[0,0,0],[0,0],[0]],[[141734367,64560240,645894],[64560240,2583576],[645894]],[[0,0,0],[0,0],[0]],[[523206216,89951310,291600],[89951310,1166400],[291600]],[[0,0,0],[0,0],[0]],[[1195249446,86710176,78732],[86710176,314928],[78732]],[[0,0,0],[0,0],[0]],[[1903427748,59247288,11664],[59247288,46656],[11664]],[[0,0,0],[0,0],[0]],[[2226520548,28903392,729],[28903392,2916],[729]],[[0,0],[0]],[[1965480228,9994590],[9994590]],[[0,0],[0]],[[1327619808,2391120],[2391120]],[[0,0],[0]],[[689721480,376164],[376164]],[[0,0],[0]],[[275030559,34992],[34992]],[[0,0],[0]],[[83385936,1458],[1458]],[[0]],[[18865062]],[[0]],[[3082212]],[[0]],[[343359]],[[0]],[[23328]],[[0]],[[729]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
