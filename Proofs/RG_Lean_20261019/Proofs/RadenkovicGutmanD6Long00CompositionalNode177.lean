/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode174
import Proofs.RadenkovicGutmanD6Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-8],[0]],[[0,0],[0]],[[-136,0],[0,0]],[[0,0],[0,0]],[[-976,0],[0,0]],[[0,0],[0,0]],[[-3848,0],[0,0]],[[0,0],[0,0]],[[-9088,0],[0,0]],[[0,0],[0,0]],[[-13152,-8],[-8,0]],[[0,0],[0,0]],[[-11440,-64],[-64,0]],[[0,0],[0,0]],[[-5576,-176],[-176,0]],[[0,0],[0,0]],[[-1272,-192],[-192,0]],[[0,0],[0,0]],[[-72,-72],[-72,0]],[[0],[0,0]],[[0],[0,-8]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
