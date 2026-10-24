/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode021
import Proofs.RadenkovicGutmanD3Long00StagedUNode022
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e023 : NestedArithmetic.Expr 3 := .plus e021 e022
noncomputable def p023 : NestedHorner.Poly 3 := [[[],[1]],[[0]],[[9]],[[0]],[[24]],[[0]],[[22]],[[0]],[[8]],[[0]],[[1]]]
theorem step023 : p023=NestedHorner.add p021 p022 := by decide +kernel
#print axioms step023
theorem h023 : NestedArithmetic.compile e023=p023 := by
  change NestedHorner.add (NestedArithmetic.compile e021) (NestedArithmetic.compile e022)=p023
  rw [h021,h022]
  exact step023.symm
#print axioms h023
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
