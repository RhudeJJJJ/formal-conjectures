/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode171
import Proofs.RadenkovicGutmanD17Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[34,0],[0]],[[0,0],[0]],[[510,0],[0]],[[0,0],[0]],[[3196,0],[0]],[[0,0],[0]],[[10846,0],[0]],[[0,0],[0]],[[21624,0],[0]],[[0,0],[0]],[[25738,17],[17]],[[0,0],[0]],[[17748,119],[119]],[[0,0],[0]],[[6426,272],[272]],[[0,0],[0]],[[918,221],[221]],[[0,0],[0]],[[0,51],[51]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
