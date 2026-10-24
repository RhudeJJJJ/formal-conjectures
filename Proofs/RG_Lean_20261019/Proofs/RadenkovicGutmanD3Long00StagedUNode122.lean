/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode002
import Proofs.RadenkovicGutmanD3Long00StagedUNode118
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e122 : NestedArithmetic.Expr 3 := .times e002 e118
noncomputable def p122 : NestedHorner.Poly 3 := [[[3]]]
theorem step122 : p122=NestedArithmetic.mul p002 p118 := by decide +kernel
#print axioms step122
theorem h122 : NestedArithmetic.compile e122=p122 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e002) (NestedArithmetic.compile e118)=p122
  rw [h002,h118]
  exact step122.symm
#print axioms h122
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
