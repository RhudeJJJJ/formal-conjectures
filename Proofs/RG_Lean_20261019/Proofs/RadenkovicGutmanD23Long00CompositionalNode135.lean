/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode002
import Proofs.RadenkovicGutmanD23Long00CompositionalNode001
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e135 : NestedArithmetic.Expr 3 := .times e002 e001
noncomputable def p135 : NestedHorner.Poly 3 := [[[]],[[0]],[[0]],[[0]],[[3]]]
theorem step135 : p135=NestedArithmetic.mul p002 p001 := by decide +kernel
#print axioms step135
theorem h135 : NestedArithmetic.compile e135=p135 := StagedExprCompile.compile_times e135 e002 e001 p002 p001 p135 rfl h002 h001 step135
#print axioms h135
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
