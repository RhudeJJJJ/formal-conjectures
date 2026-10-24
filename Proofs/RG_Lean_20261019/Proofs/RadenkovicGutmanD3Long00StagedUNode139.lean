/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode121
import Proofs.RadenkovicGutmanD3Long00StagedUNode138
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e139 : NestedArithmetic.Expr 3 := .plus e121 e138
noncomputable def p139 : NestedHorner.Poly 3 := [[[1]],[[0]],[[2]]]
theorem step139 : p139=NestedHorner.add p121 p138 := by decide +kernel
#print axioms step139
theorem h139 : NestedArithmetic.compile e139=p139 := by
  change NestedHorner.add (NestedArithmetic.compile e121) (NestedArithmetic.compile e138)=p139
  rw [h121,h138]
  exact step139.symm
#print axioms h139
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
