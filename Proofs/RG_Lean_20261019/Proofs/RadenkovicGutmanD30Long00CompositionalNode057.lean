/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode034
import Proofs.RadenkovicGutmanD30Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-90],[-90]],[[0,0],[0]],[[-1350,-390],[-390]],[[0,0],[0]],[[-9000,-480],[-480]],[[0,0],[0]],[[-23370,-210],[-210]],[[0,0],[0]],[[-31680,-30],[-30]],[[0]],[[-24840]],[[0]],[[-11640]],[[0]],[[-3210]],[[0]],[[-480]],[[0]],[[-30]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
