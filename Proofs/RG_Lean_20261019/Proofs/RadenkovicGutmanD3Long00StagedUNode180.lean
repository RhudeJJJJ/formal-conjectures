/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode179
import Proofs.RadenkovicGutmanD3Long00StagedUNode120
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e180 : NestedArithmetic.Expr 3 := .times e179 e120
noncomputable def p180 : NestedHorner.Poly 3 := [[[-1]],[[0]],[[-14]],[[0]],[[-81]],[[0]],[[-250]],[[0]],[[-444]],[[0]],[[-458]],[[0]],[[-265]],[[0]],[[-78]],[[0]],[[-9]]]
theorem step180 : p180=NestedArithmetic.mul p179 p120 := by decide +kernel
#print axioms step180
theorem h180 : NestedArithmetic.compile e180=p180 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e179) (NestedArithmetic.compile e120)=p180
  rw [h179,h120]
  exact step180.symm
#print axioms h180
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
