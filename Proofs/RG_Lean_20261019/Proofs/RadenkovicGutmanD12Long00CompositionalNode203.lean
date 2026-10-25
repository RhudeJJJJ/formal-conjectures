/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode202
import Proofs.RadenkovicGutmanD12Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[46,0],[0,0]],[[0,0],[0,0]],[[448,0],[0,0]],[[0,0],[0,0]],[[2426,0],[0,0]],[[0,0],[0,0]],[[8044,0],[0,0]],[[0,0],[0,0]],[[16920,2],[2,0]],[[0,0],[0,0]],[[22588,28],[28,0]],[[0,0],[0,0]],[[18554,140],[140,0]],[[0,0],[0,0]],[[8682,312],[312,0]],[[0,0],[0,0]],[[1926,306],[306,0]],[[0,0],[0,0]],[[108,108],[108,2]],[[0],[0,0]],[[0],[0,12]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
