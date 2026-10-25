/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode159
import Proofs.RadenkovicGutmanD31Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-29],[0]],[[0,0],[0]],[[-435,0],[0,0]],[[0,0],[0,0]],[[-2726,0],[0,0]],[[0,0],[0,0]],[[-9251,0],[0,0]],[[0,0],[0,0]],[[-18444,0],[0,0]],[[0,0],[0,0]],[[-21924,-29],[-29,0]],[[0,0],[0,0]],[[-14906,-232],[-232,0]],[[0,0],[0,0]],[[-4843,-638],[-638,0]],[[0,0],[0,0]],[[-87,-696],[-696,0]],[[0,0],[0,0]],[[261,-261],[-261,0]],[[0],[0,0]],[[0],[0,-29]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
