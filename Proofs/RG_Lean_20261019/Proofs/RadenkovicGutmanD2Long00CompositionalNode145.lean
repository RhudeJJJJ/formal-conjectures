/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode022
import Proofs.RadenkovicGutmanD2Long00CompositionalNode144
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e145 : NestedArithmetic.Expr 3 := .times e022 e144
noncomputable def p145 : NestedHorner.Poly 3 := [[[],[]],[[],[0]],[[],[0]],[[],[0]],[[],[0]],[[],[0]],[[],[0]],[[],[0]],[[],[0]],[[],[0]],[[],[1]]]
theorem step145 : p145=NestedArithmetic.mul p022 p144 := by decide +kernel
#print axioms step145
theorem h145 : NestedArithmetic.compile e145=p145 := StagedExprCompile.compile_times e145 e022 e144 p022 p144 p145 rfl h022 h144 step145
#print axioms h145
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
