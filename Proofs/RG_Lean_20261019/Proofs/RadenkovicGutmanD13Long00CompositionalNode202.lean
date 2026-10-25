/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode191
import Proofs.RadenkovicGutmanD13Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[47,0],[0,0]],[[0,0],[0,0]],[[465,0],[0,0]],[[0,0],[0,0]],[[2548,0],[0,0]],[[0,0],[0,0]],[[8525,0],[0,0]],[[0,0],[0,0]],[[18056,2],[2,0]],[[0,0],[0,0]],[[24232,29],[29,0]],[[0,0],[0,0]],[[19984,148],[148,0]],[[0,0],[0,0]],[[9379,334],[334,0]],[[0,0],[0,0]],[[2085,330],[330,0]],[[0,0],[0,0]],[[117,117],[117,2]],[[0],[0,0]],[[0],[0,13]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
