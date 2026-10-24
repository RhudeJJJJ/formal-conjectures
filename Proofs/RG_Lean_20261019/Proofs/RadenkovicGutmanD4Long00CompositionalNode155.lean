/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode154
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e155 : NestedArithmetic.Expr 3 := .scaled (-1) e154
noncomputable def p155 : NestedHorner.Poly 3 := [[[-1]],[[0]],[[-14]],[[0]],[[-81]],[[0]],[[-250]],[[0]],[[-444]],[[0]],[[-458]],[[0]],[[-265]],[[0]],[[-78]],[[0]],[[-9]]]
theorem step155 : p155=NestedHorner.scale (-1) p154 := by decide +kernel
#print axioms step155
theorem h155 : NestedArithmetic.compile e155=p155 := StagedExprCompile.compile_scaled (-1) e155 e154 p154 p155 rfl h154 step155
#print axioms h155
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
