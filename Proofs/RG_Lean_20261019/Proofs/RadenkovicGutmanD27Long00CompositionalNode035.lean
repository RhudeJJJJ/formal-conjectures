/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode034
import Proofs.RadenkovicGutmanD27Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-81],[-81]],[[0,0],[0]],[[-1458,-351],[-351]],[[0,0],[0]],[[-10206,-432],[-432]],[[0,0],[0]],[[-28188,-189],[-189]],[[0,0],[0]],[[-40878,-27],[-27]],[[0]],[[-34344]],[[0]],[[-17226]],[[0]],[[-5076]],[[0]],[[-810]],[[0]],[[-54]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
