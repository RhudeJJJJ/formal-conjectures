/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode034
import Proofs.RadenkovicGutmanD45Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-90],[0]],[[0,0],[0]],[[-1350,0],[0]],[[0,0],[0]],[[-8460,0],[0]],[[0,0],[0]],[[-28710,0],[0]],[[0,0],[0]],[[-57240,0],[0]],[[0,0],[0]],[[-68130,-45],[-45]],[[0,0],[0]],[[-46980,-315],[-315]],[[0,0],[0]],[[-17010,-720],[-720]],[[0,0],[0]],[[-2430,-585],[-585]],[[0,0],[0]],[[0,-135],[-135]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
