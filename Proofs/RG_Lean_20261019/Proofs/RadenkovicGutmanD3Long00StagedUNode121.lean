/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode119
import Proofs.RadenkovicGutmanD3Long00StagedUNode120
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e121 : NestedArithmetic.Expr 3 := .times e119 e120
noncomputable def p121 : NestedHorner.Poly 3 := [[[1]]]
theorem step121 : p121=NestedArithmetic.mul p119 p120 := by decide +kernel
#print axioms step121
theorem h121 : NestedArithmetic.compile e121=p121 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e119) (NestedArithmetic.compile e120)=p121
  rw [h119,h120]
  exact step121.symm
#print axioms h121
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
