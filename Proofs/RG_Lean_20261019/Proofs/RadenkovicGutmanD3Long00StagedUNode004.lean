/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode002
import Proofs.RadenkovicGutmanD3Long00StagedUNode003
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e004 : NestedArithmetic.Expr 3 := .times e002 e003
noncomputable def p004 : NestedHorner.Poly 3 := [[[]],[[0]],[[3]]]
theorem step004 : p004=NestedArithmetic.mul p002 p003 := by decide +kernel
#print axioms step004
theorem h004 : NestedArithmetic.compile e004=p004 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e002) (NestedArithmetic.compile e003)=p004
  rw [h002,h003]
  exact step004.symm
#print axioms h004
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
