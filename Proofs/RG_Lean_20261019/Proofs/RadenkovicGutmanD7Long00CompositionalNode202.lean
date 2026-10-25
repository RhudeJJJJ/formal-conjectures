/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode191
import Proofs.RadenkovicGutmanD7Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[41,0],[0,0]],[[0,0],[0,0]],[[363,0],[0,0]],[[0,0],[0,0]],[[1816,0],[0,0]],[[0,0],[0,0]],[[5639,0],[0,0]],[[0,0],[0,0]],[[11240,2],[2,0]],[[0,0],[0,0]],[[14368,23],[23,0]],[[0,0],[0,0]],[[11404,100],[100,0]],[[0,0],[0,0]],[[5197,202],[202,0]],[[0,0],[0,0]],[[1131,186],[186,0]],[[0,0],[0,0]],[[63,63],[63,2]],[[0],[0,0]],[[0],[0,7]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
