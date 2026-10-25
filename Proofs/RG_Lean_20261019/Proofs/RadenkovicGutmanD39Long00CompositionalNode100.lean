/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode043
import Proofs.RadenkovicGutmanD39Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-13689],[0,-27378,8658],[-13689,8658]],[[0,0,0],[0,0,0],[0,0]],[[0,-538083,-40716],[-538083,48438,37518],[-40716,37518]],[[0,0,0],[0,0,0],[0,0]],[[-4991220,-4303611,142389],[-4303611,1150578,46176],[142389,46176]],[[0,0,0],[0,0,0],[0,0]],[[-59852520,-12691107,809874],[-12691107,3867942,20202],[809874,20202]],[[0,0,0],[0,0,0],[0,0]],[[-317077254,-12696996,1509378],[-12696996,6066372,2886],[1509378,2886]],[[0,0,0],[0,0],[0]],[[-977112630,19145529,1455246],[19145529,5300100],[1455246]],[[0,0,0],[0,0],[0]],[[-1925280942,78039273,797433],[78039273,2714634],[797433]],[[0,0,0],[0,0],[0]],[[-2468899992,118462032,249990],[118462032,808782],[249990]],[[0,0,0],[0,0],[0]],[[-1893262878,107778723,41769],[107778723,129714],[41769]],[[0,0,0],[0,0],[0]],[[-402348804,64676313,2886],[64676313,8658],[2886]],[[0,0],[0]],[[953880408,26258466],[26258466]],[[0,0],[0]],[[1399304790,7152795],[7152795]],[[0,0],[0]],[[1070675190,1253733],[1253733]],[[0,0],[0]],[[549092466,127881],[127881]],[[0,0],[0]],[[199883034,5772],[5772]],[[0]],[[52100100]],[[0]],[[9542910]],[[0]],[[1169064]],[[0]],[[86112]],[[0]],[[2886]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
