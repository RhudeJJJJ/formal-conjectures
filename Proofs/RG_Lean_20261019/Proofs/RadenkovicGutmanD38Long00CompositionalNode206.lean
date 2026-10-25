/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode203
import Proofs.RadenkovicGutmanD38Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[148,0],[0,0]],[[0,0],[0,0]],[[2106,0],[0,0]],[[0,0],[0,0]],[[13730,0],[0,0]],[[0,0],[0,0]],[[50038,0],[0,0]],[[0,0],[0,0]],[[109384,2],[2,0]],[[0,0],[0,0]],[[145588,130],[130,0]],[[0,0],[0,0]],[[114938,880],[880,0]],[[0,0],[0,0]],[[49604,2100],[2100,0]],[[0,0],[0,0]],[[9480,1918],[1918,0]],[[0,0],[0,0]],[[342,570],[570,2]],[[0],[0,0]],[[0],[0,38]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
