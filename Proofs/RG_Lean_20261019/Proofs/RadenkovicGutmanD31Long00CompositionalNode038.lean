/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode037
import Proofs.RadenkovicGutmanD31Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-29]],[[0,0],[0]],[[261,-261],[-261]],[[0,0],[0]],[[-87,-696],[-696]],[[0,0],[0]],[[-4843,-638],[-638]],[[0,0],[0]],[[-14906,-232],[-232]],[[0,0],[0]],[[-21924,-29],[-29]],[[0]],[[-18444]],[[0]],[[-9251]],[[0]],[[-2726]],[[0]],[[-435]],[[0]],[[-29]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
