/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode044
import Proofs.RadenkovicGutmanD13Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,13]],[[0,0],[0,0]],[[117,117],[117,2]],[[0,0],[0]],[[2085,330],[330]],[[0,0],[0]],[[9379,334],[334]],[[0,0],[0]],[[19984,148],[148]],[[0,0],[0]],[[24232,29],[29]],[[0,0],[0]],[[18056,2],[2]],[[0]],[[8525]],[[0]],[[2548]],[[0]],[[465]],[[0]],[[47]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
