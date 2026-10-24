/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode006
import Proofs.RadenkovicGutmanD2Long00CompositionalNode001
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e126 : NestedArithmetic.Expr 3 := .times e006 e001
noncomputable def p126 : NestedHorner.Poly 3 := [[[]],[[0]],[[0]],[[0]],[[1]]]
theorem step126 : p126=NestedArithmetic.mul p006 p001 := by decide +kernel
#print axioms step126
theorem h126 : NestedArithmetic.compile e126=p126 := StagedExprCompile.compile_times e126 e006 e001 p006 p001 p126 rfl h006 h001 step126
#print axioms h126
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
