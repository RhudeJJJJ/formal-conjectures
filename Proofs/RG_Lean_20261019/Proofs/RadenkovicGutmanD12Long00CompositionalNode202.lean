/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode191
import Proofs.RadenkovicGutmanD12Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[46,0],[0,0]],[[0,0],[0,0]],[[448,0],[0,0]],[[0,0],[0,0]],[[2426,0],[0,0]],[[0,0],[0,0]],[[8044,0],[0,0]],[[0,0],[0,0]],[[16920,2],[2,0]],[[0,0],[0,0]],[[22588,28],[28,0]],[[0,0],[0,0]],[[18554,140],[140,0]],[[0,0],[0,0]],[[8682,312],[312,0]],[[0,0],[0,0]],[[1926,306],[306,0]],[[0,0],[0,0]],[[108,108],[108,2]],[[0],[0,0]],[[0],[0,12]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
