/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode035
import Proofs.RadenkovicGutmanD3Long00StagedUNode036
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e035 e036
noncomputable def p057 : NestedHorner.Poly 3 := [[[]],[[-2]]]
theorem step057 : p057=NestedArithmetic.mul p035 p036 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e035) (NestedArithmetic.compile e036)=p057
  rw [h035,h036]
  exact step057.symm
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
