/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode034
import Proofs.RadenkovicGutmanD45Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-135],[-135]],[[0,0],[0]],[[-2430,-585],[-585]],[[0,0],[0]],[[-17010,-720],[-720]],[[0,0],[0]],[[-46980,-315],[-315]],[[0,0],[0]],[[-68130,-45],[-45]],[[0]],[[-57240]],[[0]],[[-28710]],[[0]],[[-8460]],[[0]],[[-1350]],[[0]],[[-90]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
