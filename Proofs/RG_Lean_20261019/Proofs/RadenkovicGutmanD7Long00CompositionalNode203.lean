/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode202
import Proofs.RadenkovicGutmanD7Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[41,0],[0,0]],[[0,0],[0,0]],[[363,0],[0,0]],[[0,0],[0,0]],[[1816,0],[0,0]],[[0,0],[0,0]],[[5639,0],[0,0]],[[0,0],[0,0]],[[11240,2],[2,0]],[[0,0],[0,0]],[[14368,23],[23,0]],[[0,0],[0,0]],[[11404,100],[100,0]],[[0,0],[0,0]],[[5197,202],[202,0]],[[0,0],[0,0]],[[1131,186],[186,0]],[[0,0],[0,0]],[[63,63],[63,2]],[[0],[0,0]],[[0],[0,7]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
