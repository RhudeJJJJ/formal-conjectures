/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode033
import Proofs.RadenkovicGutmanD10Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,100]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,2400],[0,2400,20]],[[0,0,0],[0,0,0],[0,0]],[[-8100,-5400,13500],[-5400,52200,7760],[13500,7760]],[[0,0,0],[0,0,0],[0,0]],[[-223020,205200,82620],[205200,314880,8560],[82620,8560]],[[0,0,0],[0,0,0],[0,0]],[[-970380,2030760,210240],[2030760,787960,3880],[210240,3880]],[[0,0,0],[0,0,0],[0,0]],[[2234940,8192680,290840],[8192680,1071760,720],[290840,720]],[[0,0,0],[0,0,0],[0,0]],[[33062900,19050720,239800],[19050720,870400,40],[239800,40]],[[0,0,0],[0,0],[0]],[[138464660,28812400,121520],[28812400,436080],[121520]],[[0,0,0],[0,0],[0]],[[344545480,30005000,37600],[30005000,134200],[37600]],[[0,0,0],[0,0],[0]],[[588960680,22131880,6760],[22131880,24240],[6760]],[[0,0,0],[0,0],[0]],[[734496440,11691640,620],[11691640,2280],[620]],[[0,0,0],[0,0],[0]],[[689157440,4413960,20],[4413960,80],[20]],[[0,0],[0]],[[494486640,1172200],[1172200]],[[0,0],[0]],[[273321440,211600],[211600]],[[0,0],[0]],[[116426500,24320],[24320]],[[0,0],[0]],[[37986420,1560],[1560]],[[0,0],[0]],[[9364680,40],[40]],[[0]],[[1703560]],[[0]],[[219860]],[[0]],[[18820]],[[0]],[[940]],[[0]],[[20]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
