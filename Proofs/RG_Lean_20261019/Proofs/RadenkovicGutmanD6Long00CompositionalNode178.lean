/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode177
import Proofs.RadenkovicGutmanD6Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-8],[0]],[[0,0],[0]],[[-136,0],[0,0]],[[0,0],[0,0]],[[-976,0],[0,0]],[[0,0],[0,0]],[[-3848,0],[0,0]],[[0,0],[0,0]],[[-9088,0],[0,0]],[[0,0],[0,0]],[[-13152,-8],[-8,0]],[[0,0],[0,0]],[[-11440,-64],[-64,0]],[[0,0],[0,0]],[[-5576,-176],[-176,0]],[[0,0],[0,0]],[[-1272,-192],[-192,0]],[[0,0],[0,0]],[[-72,-72],[-72,0]],[[0],[0,0]],[[0],[0,-8]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
