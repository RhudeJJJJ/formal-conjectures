/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode034
import Proofs.RadenkovicGutmanD35Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-105],[-105]],[[0,0],[0]],[[-1575,-455],[-455]],[[0,0],[0]],[[-10500,-560],[-560]],[[0,0],[0]],[[-27265,-245],[-245]],[[0,0],[0]],[[-36960,-35],[-35]],[[0]],[[-28980]],[[0]],[[-13580]],[[0]],[[-3745]],[[0]],[[-560]],[[0]],[[-35]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
