/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode001
import Proofs.RadenkovicGutmanD35Long00CompositionalNode010
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e011 : NestedArithmetic.Expr 3 := .plus e001 e010
noncomputable def p011 : NestedHorner.Poly 3 := [[[]],[[0]],[[4]],[[0]],[[1]]]
theorem step011 : p011=NestedHorner.add p001 p010 := by decide +kernel
#print axioms step011
theorem h011 : NestedArithmetic.compile e011=p011 := StagedExprCompile.compile_plus e011 e001 e010 p001 p010 p011 rfl h001 h010 step011
#print axioms h011
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
