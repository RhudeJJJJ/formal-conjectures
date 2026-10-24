/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode179
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e180 : NestedArithmetic.Expr 3 := .scaled (-1) e179
noncomputable def p180 : NestedHorner.Poly 3 := [[[-1]],[[0]],[[-14]],[[0]],[[-81]],[[0]],[[-250]],[[0]],[[-444]],[[0]],[[-458]],[[0]],[[-265]],[[0]],[[-78]],[[0]],[[-9]]]
theorem step180 : p180=NestedHorner.scale (-1) p179 := by decide +kernel
#print axioms step180
theorem h180 : NestedArithmetic.compile e180=p180 := StagedExprCompile.compile_scaled (-1) e180 e179 p179 p180 rfl h179 step180
#print axioms h180
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
