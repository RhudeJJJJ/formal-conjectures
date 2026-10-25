/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode075
import Proofs.RadenkovicGutmanD40Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1600]],[[0,0],[0,0,0],[0,0]],[[0,0,14400],[0,28800,28800],[14400,28800]],[[0,0,0],[0,0,0],[0,0]],[[-129600,475200,254400],[475200,768000,76800],[254400,76800]],[[0,0,0],[0,0,0],[0,0]],[[1641600,7646400,1115200],[7646400,3612800,70400],[1115200,70400]],[[0,0,0],[0,0,0],[0,0]],[[46267200,44049600,2288000],[44049600,7686400,25600],[2288000,25600]],[[0,0,0],[0,0,0],[0,0]],[[356553600,135593600,2630400],[135593600,9100800,3200],[2630400,3200]],[[0,0,0],[0,0],[0]],[[1483582400,259652800,1817600],[259652800,6470400],[1817600]],[[0,0,0],[0,0],[0]],[[3978080000,333323200,769600],[333323200,2819200],[769600]],[[0,0,0],[0,0],[0]],[[7465104000,298528000,195200],[298528000,736000],[195200]],[[0,0,0],[0,0],[0]],[[10267868800,190289600,27200],[190289600,105600],[27200]],[[0,0,0],[0,0],[0]],[[10643472000,86811200,1600],[86811200,6400],[1600]],[[0,0],[0]],[[8454176000,28121600],[28121600]],[[0,0],[0]],[[5191248000,6312000],[6312000]],[[0,0],[0]],[[2470300800,932800],[932800]],[[0,0],[0]],[[907678400,81600],[81600]],[[0,0],[0]],[[254841600,3200],[3200]],[[0]],[[53616000]],[[0]],[[8176000]],[[0]],[[852800]],[[0]],[[54400]],[[0]],[[1600]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
