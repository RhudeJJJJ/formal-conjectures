/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode038
import Proofs.RadenkovicGutmanD27Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-25]],[[0,0],[0]],[[261,-225],[-225]],[[0,0],[0]],[[237,-600],[-600]],[[0,0],[0]],[[-3115,-550],[-550]],[[0,0],[0]],[[-11018,-200],[-200]],[[0,0],[0]],[[-17124,-25],[-25]],[[0]],[[-14900]],[[0]],[[-7651]],[[0]],[[-2294]],[[0]],[[-371]],[[0]],[[-25]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
