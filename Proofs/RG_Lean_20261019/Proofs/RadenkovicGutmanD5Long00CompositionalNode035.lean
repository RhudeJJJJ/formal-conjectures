/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode034
import Proofs.RadenkovicGutmanD5Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-15],[-15]],[[0,0],[0]],[[-270,-65],[-65]],[[0,0],[0]],[[-1890,-80],[-80]],[[0,0],[0]],[[-5220,-35],[-35]],[[0,0],[0]],[[-7570,-5],[-5]],[[0]],[[-6360]],[[0]],[[-3190]],[[0]],[[-940]],[[0]],[[-150]],[[0]],[[-10]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
