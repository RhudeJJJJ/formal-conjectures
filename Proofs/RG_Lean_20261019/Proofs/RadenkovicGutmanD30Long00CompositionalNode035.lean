/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode034
import Proofs.RadenkovicGutmanD30Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-90],[-90]],[[0,0],[0]],[[-1620,-390],[-390]],[[0,0],[0]],[[-11340,-480],[-480]],[[0,0],[0]],[[-31320,-210],[-210]],[[0,0],[0]],[[-45420,-30],[-30]],[[0]],[[-38160]],[[0]],[[-19140]],[[0]],[[-5640]],[[0]],[[-900]],[[0]],[[-60]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
