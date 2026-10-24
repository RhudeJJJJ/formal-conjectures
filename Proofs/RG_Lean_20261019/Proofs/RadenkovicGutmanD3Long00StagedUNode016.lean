/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode015
import Proofs.RadenkovicGutmanD3Long00StagedUNode012
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e016 : NestedArithmetic.Expr 3 := .times e015 e012
noncomputable def p016 : NestedHorner.Poly 3 := [[],[[]],[[3]],[[0]],[[13]],[[0]],[[16]],[[0]],[[7]],[[0]],[[1]]]
theorem step016 : p016=NestedArithmetic.mul p015 p012 := by decide +kernel
#print axioms step016
theorem h016 : NestedArithmetic.compile e016=p016 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e015) (NestedArithmetic.compile e012)=p016
  rw [h015,h012]
  exact step016.symm
#print axioms h016
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
