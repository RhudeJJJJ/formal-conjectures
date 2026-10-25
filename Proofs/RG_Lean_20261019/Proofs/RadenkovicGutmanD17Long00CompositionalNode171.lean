/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode030
import Proofs.RadenkovicGutmanD17Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[34],[0]],[[0,0],[0]],[[510,0],[0]],[[0,0],[0]],[[3196,0],[0]],[[0,0],[0]],[[10846,0],[0]],[[0,0],[0]],[[21624,0],[0]],[[0,0],[0]],[[25738,17],[17]],[[0,0],[0]],[[17748,119],[119]],[[0,0],[0]],[[6426,272],[272]],[[0,0],[0]],[[918,221],[221]],[[0,0],[0]],[[0,51],[51]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
