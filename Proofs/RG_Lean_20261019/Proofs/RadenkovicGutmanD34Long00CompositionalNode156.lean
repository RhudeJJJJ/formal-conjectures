/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode155
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e156 : NestedArithmetic.Expr 3 := .scaled (-1) e155
noncomputable def p156 : NestedHorner.Poly 3 := [[[-1]],[[0]],[[-14]],[[0]],[[-81]],[[0]],[[-250]],[[0]],[[-444]],[[0]],[[-458]],[[0]],[[-265]],[[0]],[[-78]],[[0]],[[-9]]]
theorem step156 : p156=NestedHorner.scale (-1) p155 := by decide +kernel
#print axioms step156
theorem h156 : NestedArithmetic.compile e156=p156 := StagedExprCompile.compile_scaled (-1) e156 e155 p155 p156 rfl h155 step156
#print axioms h156
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
