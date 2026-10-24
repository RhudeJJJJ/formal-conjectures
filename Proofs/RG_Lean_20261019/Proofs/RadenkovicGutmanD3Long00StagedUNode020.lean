/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode019
import Proofs.RadenkovicGutmanD3Long00StagedUNode012
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e020 : NestedArithmetic.Expr 3 := .times e019 e012
noncomputable def p020 : NestedHorner.Poly 3 := [[[]],[[0]],[[6]],[[0]],[[11]],[[0]],[[6]],[[0]],[[1]]]
theorem step020 : p020=NestedArithmetic.mul p019 p012 := by decide +kernel
#print axioms step020
theorem h020 : NestedArithmetic.compile e020=p020 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e019) (NestedArithmetic.compile e012)=p020
  rw [h019,h012]
  exact step020.symm
#print axioms h020
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
