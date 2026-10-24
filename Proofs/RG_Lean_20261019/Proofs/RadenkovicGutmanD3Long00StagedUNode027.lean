/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode026
import Proofs.RadenkovicGutmanD3Long00StagedUNode013
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e027 : NestedArithmetic.Expr 3 := .times e026 e013
noncomputable def p027 : NestedHorner.Poly 3 := [[[]],[[0,3]],[[0,0]],[[27,13]],[[0,0]],[[189,16]],[[0,0]],[[522,7]],[[0,0]],[[757,1]],[[0]],[[636]],[[0]],[[319]],[[0]],[[94]],[[0]],[[15]],[[0]],[[1]]]
theorem step027 : p027=NestedArithmetic.mul p026 p013 := by decide +kernel
#print axioms step027
theorem h027 : NestedArithmetic.compile e027=p027 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e026) (NestedArithmetic.compile e013)=p027
  rw [h026,h013]
  exact step027.symm
#print axioms h027
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
