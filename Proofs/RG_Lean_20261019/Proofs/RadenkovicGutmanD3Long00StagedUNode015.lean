/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode003
import Proofs.RadenkovicGutmanD3Long00StagedUNode007
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e015 : NestedArithmetic.Expr 3 := .times e003 e007
noncomputable def p015 : NestedHorner.Poly 3 := [[],[[]],[[1]],[[0]],[[3]],[[0]],[[1]]]
theorem step015 : p015=NestedArithmetic.mul p003 p007 := by decide +kernel
#print axioms step015
theorem h015 : NestedArithmetic.compile e015=p015 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e003) (NestedArithmetic.compile e007)=p015
  rw [h003,h007]
  exact step015.symm
#print axioms h015
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
