/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode035
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e114 : NestedArithmetic.Expr 3 := .pow e035 2
noncomputable def p114 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,225],[0,450],[225]],[[0,0,0],[0,0],[0]],[[0,8100,1950],[8100,3900],[1950]],[[0,0,0],[0,0],[0]],[[72900,91800,6625],[91800,13250],[6625]],[[0,0,0],[0,0],[0]],[[1020600,445500,11450],[445500,22900],[11450]],[[0,0,0],[0,0],[0]],[[6390900,1227000,11100],[1227000,22200],[11100]],[[0,0,0],[0,0],[0]],[[23819400,2145100,6250],[2145100,12500],[6250]],[[0,0,0],[0,0],[0]],[[59297400,2518000,2025],[2518000,4050],[2025]],[[0,0,0],[0,0],[0]],[[104794200,2042600,350],[2042600,700],[350]],[[0,0,0],[0,0],[0]],[[136269100,1158000,25],[1158000,50],[25]],[[0,0],[0]],[[133228200,457100],[457100]],[[0,0],[0]],[[99132200,123000],[123000]],[[0,0],[0]],[[56412200,21500],[21500]],[[0,0],[0]],[[24508300,2200],[2200]],[[0,0],[0]],[[8056600,100],[100]],[[0]],[[1967800]],[[0]],[[345800]],[[0]],[[41300]],[[0]],[[3000]],[[0]],[[100]]]
theorem step114 : p114=NestedArithmetic.power p035 2 := by decide +kernel
#print axioms step114
theorem h114 : NestedArithmetic.compile e114=p114 := StagedExprCompile.compile_pow 2 e114 e035 p035 p114 rfl h035 step114
#print axioms h114
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
