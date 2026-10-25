/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode018
import Proofs.RadenkovicGutmanD6Long00CompositionalNode030
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e044 : NestedArithmetic.Expr 3 := .plus e018 e030
noncomputable def p044 : NestedHorner.Poly 3 := [[[6]],[[0]],[[2]]]
theorem step044 : p044=NestedHorner.add p018 p030 := by decide +kernel
#print axioms step044
theorem h044 : NestedArithmetic.compile e044=p044 := StagedExprCompile.compile_plus e044 e018 e030 p018 p030 p044 rfl h018 h030 step044
#print axioms h044
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
