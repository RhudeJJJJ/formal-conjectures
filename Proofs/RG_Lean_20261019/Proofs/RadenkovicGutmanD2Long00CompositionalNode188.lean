/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode187
import Proofs.RadenkovicGutmanD2Long00CompositionalNode018
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e188 : NestedArithmetic.Expr 3 := .plus e187 e018
noncomputable def p188 : NestedHorner.Poly 3 := [[[2]],[[0]],[[2]]]
theorem step188 : p188=NestedHorner.add p187 p018 := by decide +kernel
#print axioms step188
theorem h188 : NestedArithmetic.compile e188=p188 := StagedExprCompile.compile_plus e188 e187 e018 p187 p018 p188 rfl h187 h018 step188
#print axioms h188
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
