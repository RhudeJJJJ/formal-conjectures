/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode043
import Proofs.RadenkovicGutmanD43Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-16641],[0,-33282,10578],[-16641,10578]],[[0,0,0],[0,0,0],[0,0]],[[0,-653643,-49020],[-653643,60630,45838],[-49020,45838]],[[0,0,0],[0,0,0],[0,0]],[[-6060420,-5214051,176429],[-5214051,1410658,56416],[176429,56416]],[[0,0,0],[0,0,0],[0,0]],[[-72585720,-15285339,993730],[-15285339,4734214,24682],[993730,24682]],[[0,0,0],[0,0,0],[0,0]],[[-383935734,-14885396,1848226],[-14885396,7419908,3526],[1848226,3526]],[[0,0,0],[0,0],[0]],[[-1180647990,24525953,1780286],[24525953,6480100],[1780286]],[[0,0,0],[0,0],[0]],[[-2318918190,96721921,975025],[96721921,3318138],[975025]],[[0,0,0],[0,0],[0]],[[-2956689976,145884208,305558],[145884208,988398],[305558]],[[0,0,0],[0,0],[0]],[[-2234628558,132351979,51041],[132351979,158498],[51041]],[[0,0,0],[0,0],[0]],[[-414273524,79291441,3526],[79291441,10578],[3526]],[[0,0],[0]],[[1223176280,32156690],[32156690]],[[0,0],[0]],[[1742534150,8752435],[8752435]],[[0,0],[0]],[[1322395942,1533165],[1533165]],[[0,0],[0]],[[675541266,156305],[156305]],[[0,0],[0]],[[245346906,7052],[7052]],[[0]],[[63852420]],[[0]],[[11682670]],[[0]],[[1430008]],[[0]],[[105264]],[[0]],[[3526]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
