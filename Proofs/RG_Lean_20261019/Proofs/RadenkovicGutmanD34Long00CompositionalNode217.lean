/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode034
import Proofs.RadenkovicGutmanD34Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-68],[0]],[[0,0],[0]],[[-1020,0],[0]],[[0,0],[0]],[[-6392,0],[0]],[[0,0],[0]],[[-21692,0],[0]],[[0,0],[0]],[[-43248,0],[0]],[[0,0],[0]],[[-51476,-34],[-34]],[[0,0],[0]],[[-35496,-238],[-238]],[[0,0],[0]],[[-12852,-544],[-544]],[[0,0],[0]],[[-1836,-442],[-442]],[[0,0],[0]],[[0,-102],[-102]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
