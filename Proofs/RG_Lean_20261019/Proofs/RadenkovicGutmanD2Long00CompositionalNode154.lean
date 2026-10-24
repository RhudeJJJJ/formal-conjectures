/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode153
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e154 : NestedArithmetic.Expr 3 := .scaled (-1) e153
noncomputable def p154 : NestedHorner.Poly 3 := [[[-1]],[[0]],[[-14]],[[0]],[[-81]],[[0]],[[-250]],[[0]],[[-444]],[[0]],[[-458]],[[0]],[[-265]],[[0]],[[-78]],[[0]],[[-9]]]
theorem step154 : p154=NestedHorner.scale (-1) p153 := by decide +kernel
#print axioms step154
theorem h154 : NestedArithmetic.compile e154=p154 := StagedExprCompile.compile_scaled (-1) e154 e153 p153 p154 rfl h153 step154
#print axioms h154
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
