/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode045
import Proofs.RadenkovicGutmanD3Long00StagedUNode000
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e046 : NestedArithmetic.Expr 3 := .times e045 e000
noncomputable def p046 : NestedHorner.Poly 3 := [[[]],[[6]]]
theorem step046 : p046=NestedArithmetic.mul p045 p000 := by decide +kernel
#print axioms step046
theorem h046 : NestedArithmetic.compile e046=p046 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e045) (NestedArithmetic.compile e000)=p046
  rw [h045,h000]
  exact step046.symm
#print axioms h046
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
