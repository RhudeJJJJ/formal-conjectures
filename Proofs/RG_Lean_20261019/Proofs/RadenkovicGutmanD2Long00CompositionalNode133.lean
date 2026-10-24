/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode002
import Proofs.RadenkovicGutmanD2Long00CompositionalNode001
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e133 : NestedArithmetic.Expr 3 := .times e002 e001
noncomputable def p133 : NestedHorner.Poly 3 := [[[]],[[0]],[[0]],[[0]],[[3]]]
theorem step133 : p133=NestedArithmetic.mul p002 p001 := by decide +kernel
#print axioms step133
theorem h133 : NestedArithmetic.compile e133=p133 := StagedExprCompile.compile_times e133 e002 e001 p002 p001 p133 rfl h002 h001 step133
#print axioms h133
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
