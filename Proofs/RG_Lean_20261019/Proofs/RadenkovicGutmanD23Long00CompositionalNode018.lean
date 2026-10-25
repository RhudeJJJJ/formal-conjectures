/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode017
import Proofs.RadenkovicGutmanD23Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e018 : NestedArithmetic.Expr 3 := .times e017 e003
noncomputable def p018 : NestedHorner.Poly 3 := [[[]],[[0]],[[2]]]
theorem step018 : p018=NestedArithmetic.mul p017 p003 := by decide +kernel
#print axioms step018
theorem h018 : NestedArithmetic.compile e018=p018 := StagedExprCompile.compile_times e018 e017 e003 p017 p003 p018 rfl h017 h003 step018
#print axioms h018
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
