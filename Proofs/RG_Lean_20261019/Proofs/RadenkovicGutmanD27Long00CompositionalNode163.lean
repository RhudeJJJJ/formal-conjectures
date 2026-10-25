/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode160
import Proofs.RadenkovicGutmanD27Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-25],[0]],[[0,0],[0]],[[-371,0],[0,0]],[[0,0],[0,0]],[[-2294,0],[0,0]],[[0,0],[0,0]],[[-7651,0],[0,0]],[[0,0],[0,0]],[[-14900,0],[0,0]],[[0,0],[0,0]],[[-17124,-25],[-25,0]],[[0,0],[0,0]],[[-11018,-200],[-200,0]],[[0,0],[0,0]],[[-3115,-550],[-550,0]],[[0,0],[0,0]],[[237,-600],[-600,0]],[[0,0],[0,0]],[[261,-225],[-225,0]],[[0],[0,0]],[[0],[0,-25]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
