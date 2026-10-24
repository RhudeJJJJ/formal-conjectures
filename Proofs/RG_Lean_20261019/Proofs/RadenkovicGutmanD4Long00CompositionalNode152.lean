/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode006
import Proofs.RadenkovicGutmanD4Long00CompositionalNode128
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e152 : NestedArithmetic.Expr 3 := .times e006 e128
noncomputable def p152 : NestedHorner.Poly 3 := [[[1]],[[0]],[[3]],[[0]],[[1]]]
theorem step152 : p152=NestedArithmetic.mul p006 p128 := by decide +kernel
#print axioms step152
theorem h152 : NestedArithmetic.compile e152=p152 := StagedExprCompile.compile_times e152 e006 e128 p006 p128 p152 rfl h006 h128 step152
#print axioms h152
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
