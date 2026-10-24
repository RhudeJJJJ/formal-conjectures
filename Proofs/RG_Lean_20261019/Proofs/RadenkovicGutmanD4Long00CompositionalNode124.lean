/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode123
import Proofs.RadenkovicGutmanD4Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e124 : NestedArithmetic.Expr 3 := .times e123 e003
noncomputable def p124 : NestedHorner.Poly 3 := [[[]],[[0]],[[3]]]
theorem step124 : p124=NestedArithmetic.mul p123 p003 := by decide +kernel
#print axioms step124
theorem h124 : NestedArithmetic.compile e124=p124 := StagedExprCompile.compile_times e124 e123 e003 p123 p003 p124 rfl h123 h003 step124
#print axioms h124
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
