/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode165
import Proofs.RadenkovicGutmanD25Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-46],[0]],[[0,0],[0]],[[-632,0],[0,0]],[[0,0],[0,0]],[[-3462,0],[0,0]],[[0,0],[0,0]],[[-9326,0],[0,0]],[[0,0],[0,0]],[[-11306,0],[0,0]],[[0,0],[0,0]],[[576,-46],[-46,0]],[[0,0],[0,0]],[[17870,-343],[-343,0]],[[0,0],[0,0]],[[20538,-837],[-837,0]],[[0,0],[0,0]],[[9936,-704],[-704,0]],[[0,0],[0,0]],[[1836,-89],[-89,0]],[[0,0],[0,0]],[[0,75],[75,-46]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
