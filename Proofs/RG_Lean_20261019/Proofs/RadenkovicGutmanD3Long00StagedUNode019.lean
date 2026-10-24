/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode001
import Proofs.RadenkovicGutmanD3Long00StagedUNode018
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e019 : NestedArithmetic.Expr 3 := .plus e001 e018
noncomputable def p019 : NestedHorner.Poly 3 := [[[]],[[0]],[[2]],[[0]],[[1]]]
theorem step019 : p019=NestedHorner.add p001 p018 := by decide +kernel
#print axioms step019
theorem h019 : NestedArithmetic.compile e019=p019 := by
  change NestedHorner.add (NestedArithmetic.compile e001) (NestedArithmetic.compile e018)=p019
  rw [h001,h018]
  exact step019.symm
#print axioms h019
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
