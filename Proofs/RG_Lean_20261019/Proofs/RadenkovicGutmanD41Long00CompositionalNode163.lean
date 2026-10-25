/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode160
import Proofs.RadenkovicGutmanD41Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-39],[0]],[[0,0],[0]],[[-581,0],[0,0]],[[0,0],[0,0]],[[-3610,0],[0,0]],[[0,0],[0,0]],[[-12117,0],[0,0]],[[0,0],[0,0]],[[-23804,0],[0,0]],[[0,0],[0,0]],[[-27708,-39],[-39,0]],[[0,0],[0,0]],[[-18214,-312],[-312,0]],[[0,0],[0,0]],[[-5453,-858],[-858,0]],[[0,0],[0,0]],[[195,-936],[-936,0]],[[0,0],[0,0]],[[387,-351],[-351,0]],[[0],[0,0]],[[0],[0,-39]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
