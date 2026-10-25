/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode034
import Proofs.RadenkovicGutmanD34Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-102],[-102]],[[0,0],[0]],[[-1836,-442],[-442]],[[0,0],[0]],[[-12852,-544],[-544]],[[0,0],[0]],[[-35496,-238],[-238]],[[0,0],[0]],[[-51476,-34],[-34]],[[0]],[[-43248]],[[0]],[[-21692]],[[0]],[[-6392]],[[0]],[[-1020]],[[0]],[[-68]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
