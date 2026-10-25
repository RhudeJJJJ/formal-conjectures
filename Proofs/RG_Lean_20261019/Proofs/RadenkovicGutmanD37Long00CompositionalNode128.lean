/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode006
import Proofs.RadenkovicGutmanD37Long00CompositionalNode001
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e128 : NestedArithmetic.Expr 3 := .times e006 e001
noncomputable def p128 : NestedHorner.Poly 3 := [[[]],[[0]],[[0]],[[0]],[[1]]]
theorem step128 : p128=NestedArithmetic.mul p006 p001 := by decide +kernel
#print axioms step128
theorem h128 : NestedArithmetic.compile e128=p128 := StagedExprCompile.compile_times e128 e006 e001 p006 p001 p128 rfl h006 h001 step128
#print axioms h128
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
