/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode034
import Proofs.RadenkovicGutmanD41Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-123],[-123]],[[0,0],[0]],[[-1845,-533],[-533]],[[0,0],[0]],[[-12300,-656],[-656]],[[0,0],[0]],[[-31939,-287],[-287]],[[0,0],[0]],[[-43296,-41],[-41]],[[0]],[[-33948]],[[0]],[[-15908]],[[0]],[[-4387]],[[0]],[[-656]],[[0]],[[-41]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
