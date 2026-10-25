/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode097
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e098 : NestedArithmetic.Expr 3 := .scaled (-1) e097
noncomputable def p098 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1875],[0,1875]],[[0,0,0],[0,0,0],[0,0]],[[0,-16875,28125],[-16875,84375,8275],[28125,8275]],[[0,0,0],[0,0,0],[0,0]],[[-253125,558225,216975],[558225,623700,10650],[216975,10650]],[[0,0,0],[0,0,0],[0,0]],[[1454625,6811200,666950],[6811200,1835775,5175],[666950,5175]],[[0,0,0],[0,0,0],[0,0]],[[42882750,32049725,1071725],[32049725,2842400,975],[1071725,975]],[[0,0,0],[0,0,0],[0,0]],[[298650675,84491700,990350],[84491700,2551000,50],[990350,50]],[[0,0,0],[0,0],[0]],[[1132628875,141645925,543675],[141645925,1371250],[543675]],[[0,0,0],[0,0],[0]],[[2791291200,160308850,175950],[160308850,438175],[175950]],[[0,0,0],[0,0],[0]],[[4831205800,126193125,31575],[126193125,78500],[31575]],[[0,0,0],[0,0],[0]],[[6125327975,69913175,2625],[69913175,6675],[2625]],[[0,0,0],[0,0],[0]],[[5829756550,27185350,50],[27185350,150],[50]],[[0,0],[0]],[[4222556700,7281650],[7281650]],[[0,0],[0]],[[2341413500,1288250],[1288250]],[[0,0],[0]],[[993120425,138200],[138200]],[[0,0],[0]],[[319701175,7400],[7400]],[[0,0],[0]],[[76831500,100],[100]],[[0]],[[13390500]],[[0]],[[1610125]],[[0]],[[121925]],[[0]],[[4775]],[[0]],[[50]]]
theorem step098 : p098=NestedHorner.scale (-1) p097 := by decide +kernel
#print axioms step098
theorem h098 : NestedArithmetic.compile e098=p098 := StagedExprCompile.compile_scaled (-1) e098 e097 p097 p098 rfl h097 step098
#print axioms h098
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
