/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode034
import Proofs.RadenkovicGutmanD11Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-33],[-33]],[[0,0],[0]],[[-594,-143],[-143]],[[0,0],[0]],[[-4158,-176],[-176]],[[0,0],[0]],[[-11484,-77],[-77]],[[0,0],[0]],[[-16654,-11],[-11]],[[0]],[[-13992]],[[0]],[[-7018]],[[0]],[[-2068]],[[0]],[[-330]],[[0]],[[-22]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
