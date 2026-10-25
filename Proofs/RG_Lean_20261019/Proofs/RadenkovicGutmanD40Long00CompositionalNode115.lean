/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode113
import Proofs.RadenkovicGutmanD40Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1600]],[[0,0],[0,0,0],[0,0]],[[0,0,14400],[0,0,28800],[14400,28800]],[[0,0,0],[0,0,0],[0,0]],[[129600,259200,254400],[259200,518400,76800],[254400,76800]],[[0,0,0],[0,0,0],[0,0]],[[4579200,5270400,1115200],[5270400,2764800,70400],[1115200,70400]],[[0,0,0],[0,0,0],[0,0]],[[60523200,32918400,2288000],[32918400,6220800,25600],[2288000,25600]],[[0,0,0],[0,0,0],[0,0]],[[395817600,106137600,2630400],[106137600,7680000,3200],[2630400,3200]],[[0,0,0],[0,0],[0]],[[1552225600,210339200,1817600],[210339200,5670400],[1817600]],[[0,0,0],[0,0],[0]],[[4058656000,278000000,769600],[278000000,2560000],[769600]],[[0,0,0],[0,0],[0]],[[7530467200,255673600,195200],[255673600,691200],[195200]],[[0,0,0],[0,0],[0]],[[10304924800,167091200,27200],[167091200,102400],[27200]],[[0,0,0],[0,0],[0]],[[10658099200,78064000,1600],[78064000,6400],[1600]],[[0,0],[0]],[[8458112000,25872000],[25872000]],[[0,0],[0]],[[5191936000,5936000],[5936000]],[[0,0],[0]],[[2470371200,896000],[896000]],[[0,0],[0]],[[907681600,80000],[80000]],[[0,0],[0]],[[254841600,3200],[3200]],[[0]],[[53616000]],[[0]],[[8176000]],[[0]],[[852800]],[[0]],[[54400]],[[0]],[[1600]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
