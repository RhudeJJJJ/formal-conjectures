/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode152
import Proofs.RadenkovicGutmanD4Long00CompositionalNode135
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e153 : NestedArithmetic.Expr 3 := .times e152 e135
noncomputable def p153 : NestedHorner.Poly 3 := [[[1]],[[0]],[[7]],[[0]],[[16]],[[0]],[[13]],[[0]],[[3]]]
theorem step153 : p153=NestedArithmetic.mul p152 p135 := by decide +kernel
#print axioms step153
theorem h153 : NestedArithmetic.compile e153=p153 := StagedExprCompile.compile_times e153 e152 e135 p152 p135 p153 rfl h152 h135 step153
#print axioms h153
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
