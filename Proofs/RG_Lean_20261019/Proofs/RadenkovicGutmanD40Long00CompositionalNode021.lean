/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode016
import Proofs.RadenkovicGutmanD40Long00CompositionalNode020
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e021 : NestedArithmetic.Expr 3 := .plus e016 e020
noncomputable def p021 : NestedHorner.Poly 3 := [[[]],[[0]],[[9]],[[0]],[[24]],[[0]],[[22]],[[0]],[[8]],[[0]],[[1]]]
theorem step021 : p021=NestedHorner.add p016 p020 := by decide +kernel
#print axioms step021
theorem h021 : NestedArithmetic.compile e021=p021 := StagedExprCompile.compile_plus e021 e016 e020 p016 p020 p021 rfl h016 h020 step021
#print axioms h021
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
