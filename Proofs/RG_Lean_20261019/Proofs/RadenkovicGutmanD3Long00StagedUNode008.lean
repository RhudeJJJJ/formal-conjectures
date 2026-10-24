/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode000
import Proofs.RadenkovicGutmanD3Long00StagedUNode007
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e008 : NestedArithmetic.Expr 3 := .times e000 e007
noncomputable def p008 : NestedHorner.Poly 3 := [[],[[1]],[[0]],[[3]],[[0]],[[1]]]
theorem step008 : p008=NestedArithmetic.mul p000 p007 := by decide +kernel
#print axioms step008
theorem h008 : NestedArithmetic.compile e008=p008 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e000) (NestedArithmetic.compile e007)=p008
  rw [h000,h007]
  exact step008.symm
#print axioms h008
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
