/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode191
import Proofs.RadenkovicGutmanD7Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[37,0],[0,0]],[[0,0],[0,0]],[[293,0],[0,0]],[[0,0],[0,0]],[[1296,0],[0,0]],[[0,0],[0,0]],[[3505,0],[0,0]],[[0,0],[0,0]],[[5964,2],[2,0]],[[0,0],[0,0]],[[6320,23],[23,0]],[[0,0],[0,0]],[[3932,100],[100,0]],[[0,0],[0,0]],[[1175,202],[202,0]],[[0,0],[0,0]],[[3,186],[186,0]],[[0,0],[0,0]],[[-63,63],[63,2]],[[0],[0,0]],[[0],[0,7]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
