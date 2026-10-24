/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode178
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e179 : NestedArithmetic.Expr 3 := .scaled (-1) e178
noncomputable def p179 : NestedHorner.Poly 3 := [[[-1]],[[0]],[[-14]],[[0]],[[-81]],[[0]],[[-250]],[[0]],[[-444]],[[0]],[[-458]],[[0]],[[-265]],[[0]],[[-78]],[[0]],[[-9]]]
theorem step179 : p179=NestedHorner.scale (-1) p178 := by decide +kernel
#print axioms step179
theorem h179 : NestedArithmetic.compile e179=p179 := StagedExprCompile.compile_scaled (-1) e179 e178 p178 p179 rfl h178 step179
#print axioms h179
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
