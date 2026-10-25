/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode001
import Proofs.RadenkovicGutmanD29Long00CompositionalNode004
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e005 : NestedArithmetic.Expr 3 := .plus e001 e004
noncomputable def p005 : NestedHorner.Poly 3 := [[[]],[[0]],[[3]],[[0]],[[1]]]
theorem step005 : p005=NestedHorner.add p001 p004 := by decide +kernel
#print axioms step005
theorem h005 : NestedArithmetic.compile e005=p005 := StagedExprCompile.compile_plus e005 e001 e004 p001 p004 p005 rfl h001 h004 step005
#print axioms h005
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
