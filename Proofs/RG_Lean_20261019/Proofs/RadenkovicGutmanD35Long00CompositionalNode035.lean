/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode034
import Proofs.RadenkovicGutmanD35Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-105],[-105]],[[0,0],[0]],[[-1890,-455],[-455]],[[0,0],[0]],[[-13230,-560],[-560]],[[0,0],[0]],[[-36540,-245],[-245]],[[0,0],[0]],[[-52990,-35],[-35]],[[0]],[[-44520]],[[0]],[[-22330]],[[0]],[[-6580]],[[0]],[[-1050]],[[0]],[[-70]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
