/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode160
import Proofs.RadenkovicGutmanD37Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-35],[0]],[[0,0],[0]],[[-521,0],[0,0]],[[0,0],[0,0]],[[-3234,0],[0,0]],[[0,0],[0,0]],[[-10841,0],[0,0]],[[0,0],[0,0]],[[-21260,0],[0,0]],[[0,0],[0,0]],[[-24684,-35],[-35,0]],[[0,0],[0,0]],[[-16158,-280],[-280,0]],[[0,0],[0,0]],[[-4785,-770],[-770,0]],[[0,0],[0,0]],[[207,-840],[-840,0]],[[0,0],[0,0]],[[351,-315],[-315,0]],[[0],[0,0]],[[0],[0,-35]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
