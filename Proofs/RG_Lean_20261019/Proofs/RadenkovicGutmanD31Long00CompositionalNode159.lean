/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode037
import Proofs.RadenkovicGutmanD31Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-29],[0]],[[0,0],[0]],[[-435,0],[0,0]],[[0,0],[0,0]],[[-2726,0],[0,0]],[[0,0],[0,0]],[[-9251,0],[0,0]],[[0,0],[0,0]],[[-18444,0],[0,0]],[[0,0],[0,0]],[[-21924,-29],[-29,0]],[[0,0],[0,0]],[[-14906,-232],[-232,0]],[[0,0],[0,0]],[[-4843,-638],[-638,0]],[[0,0],[0,0]],[[-87,-696],[-696,0]],[[0,0],[0,0]],[[261,-261],[-261,0]],[[0],[0,0]],[[0],[0,-29]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
