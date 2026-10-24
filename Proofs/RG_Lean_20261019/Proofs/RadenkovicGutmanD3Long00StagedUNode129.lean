/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode009
import Proofs.RadenkovicGutmanD3Long00StagedUNode118
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e129 : NestedArithmetic.Expr 3 := .times e009 e118
noncomputable def p129 : NestedHorner.Poly 3 := [[[4]]]
theorem step129 : p129=NestedArithmetic.mul p009 p118 := by decide +kernel
#print axioms step129
theorem h129 : NestedArithmetic.compile e129=p129 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e009) (NestedArithmetic.compile e118)=p129
  rw [h009,h118]
  exact step129.symm
#print axioms h129
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
