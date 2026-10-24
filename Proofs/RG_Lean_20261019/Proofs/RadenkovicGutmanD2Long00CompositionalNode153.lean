/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode152
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e153 : NestedArithmetic.Expr 3 := .times e152 e152
noncomputable def p153 : NestedHorner.Poly 3 := [[[1]],[[0]],[[14]],[[0]],[[81]],[[0]],[[250]],[[0]],[[444]],[[0]],[[458]],[[0]],[[265]],[[0]],[[78]],[[0]],[[9]]]
theorem step153 : p153=NestedArithmetic.mul p152 p152 := by decide +kernel
#print axioms step153
theorem h153 : NestedArithmetic.compile e153=p153 := StagedExprCompile.compile_times e153 e152 e152 p152 p152 p153 rfl h152 h152 step153
#print axioms h153
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
