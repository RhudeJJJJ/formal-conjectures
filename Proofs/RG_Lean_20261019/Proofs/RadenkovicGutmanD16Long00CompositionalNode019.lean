/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode001
import Proofs.RadenkovicGutmanD16Long00CompositionalNode018
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e019 : NestedArithmetic.Expr 3 := .plus e001 e018
noncomputable def p019 : NestedHorner.Poly 3 := [[[]],[[0]],[[2]],[[0]],[[1]]]
theorem step019 : p019=NestedHorner.add p001 p018 := by decide +kernel
#print axioms step019
theorem h019 : NestedArithmetic.compile e019=p019 := StagedExprCompile.compile_plus e019 e001 e018 p001 p018 p019 rfl h001 h018 step019
#print axioms h019
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
