/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode122
import Proofs.RadenkovicGutmanD2Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e123 : NestedArithmetic.Expr 3 := .times e122 e003
noncomputable def p123 : NestedHorner.Poly 3 := [[[]],[[0]],[[3]]]
theorem step123 : p123=NestedArithmetic.mul p122 p003 := by decide +kernel
#print axioms step123
theorem h123 : NestedArithmetic.compile e123=p123 := StagedExprCompile.compile_times e123 e122 e003 p122 p003 p123 rfl h122 h003 step123
#print axioms h123
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
