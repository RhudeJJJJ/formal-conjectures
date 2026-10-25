/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode202
import Proofs.RadenkovicGutmanD13Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[47,0],[0,0]],[[0,0],[0,0]],[[465,0],[0,0]],[[0,0],[0,0]],[[2548,0],[0,0]],[[0,0],[0,0]],[[8525,0],[0,0]],[[0,0],[0,0]],[[18056,2],[2,0]],[[0,0],[0,0]],[[24232,29],[29,0]],[[0,0],[0,0]],[[19984,148],[148,0]],[[0,0],[0,0]],[[9379,334],[334,0]],[[0,0],[0,0]],[[2085,330],[330,0]],[[0,0],[0,0]],[[117,117],[117,2]],[[0],[0,0]],[[0],[0,13]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
