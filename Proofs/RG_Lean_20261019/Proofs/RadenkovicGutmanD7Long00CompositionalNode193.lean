/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode192
import Proofs.RadenkovicGutmanD7Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[37,0],[0,0]],[[0,0],[0,0]],[[293,0],[0,0]],[[0,0],[0,0]],[[1296,0],[0,0]],[[0,0],[0,0]],[[3505,0],[0,0]],[[0,0],[0,0]],[[5964,2],[2,0]],[[0,0],[0,0]],[[6320,23],[23,0]],[[0,0],[0,0]],[[3932,100],[100,0]],[[0,0],[0,0]],[[1175,202],[202,0]],[[0,0],[0,0]],[[3,186],[186,0]],[[0,0],[0,0]],[[-63,63],[63,2]],[[0],[0,0]],[[0],[0,7]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
