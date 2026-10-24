/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode008
import Proofs.RadenkovicGutmanD3Long00StagedUNode012
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e013 : NestedArithmetic.Expr 3 := .times e008 e012
noncomputable def p013 : NestedHorner.Poly 3 := [[],[[3]],[[0]],[[13]],[[0]],[[16]],[[0]],[[7]],[[0]],[[1]]]
theorem step013 : p013=NestedArithmetic.mul p008 p012 := by decide +kernel
#print axioms step013
theorem h013 : NestedArithmetic.compile e013=p013 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e008) (NestedArithmetic.compile e012)=p013
  rw [h008,h012]
  exact step013.symm
#print axioms h013
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
