/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode001
import Proofs.RadenkovicGutmanD3Long00StagedUNode004
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e005 : NestedArithmetic.Expr 3 := .plus e001 e004
noncomputable def p005 : NestedHorner.Poly 3 := [[[]],[[0]],[[3]],[[0]],[[1]]]
theorem step005 : p005=NestedHorner.add p001 p004 := by decide +kernel
#print axioms step005
theorem h005 : NestedArithmetic.compile e005=p005 := by
  change NestedHorner.add (NestedArithmetic.compile e001) (NestedArithmetic.compile e004)=p005
  rw [h001,h004]
  exact step005.symm
#print axioms h005
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
