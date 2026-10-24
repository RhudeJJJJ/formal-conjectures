/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode136
import Proofs.RadenkovicGutmanD2Long00CompositionalNode141
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e142 : NestedArithmetic.Expr 3 := .plus e136 e141
noncomputable def p142 : NestedHorner.Poly 3 := [[[1]],[[0]],[[8]],[[0]],[[22]],[[0]],[[24]],[[0]],[[9]]]
theorem step142 : p142=NestedHorner.add p136 p141 := by decide +kernel
#print axioms step142
theorem h142 : NestedArithmetic.compile e142=p142 := StagedExprCompile.compile_plus e142 e136 e141 p136 p141 p142 rfl h136 h141 step142
#print axioms h142
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
