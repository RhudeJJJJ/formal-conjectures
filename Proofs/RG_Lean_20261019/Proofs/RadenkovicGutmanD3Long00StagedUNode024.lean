/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode023
import Proofs.RadenkovicGutmanD3Long00StagedUNode013
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e024 : NestedArithmetic.Expr 3 := .times e023 e013
noncomputable def p024 : NestedHorner.Poly 3 := [[[],[]],[[],[3]],[[0],[0]],[[27],[13]],[[0],[0]],[[189],[16]],[[0],[0]],[[522],[7]],[[0],[0]],[[757],[1]],[[0]],[[636]],[[0]],[[319]],[[0]],[[94]],[[0]],[[15]],[[0]],[[1]]]
theorem step024 : p024=NestedArithmetic.mul p023 p013 := by decide +kernel
#print axioms step024
theorem h024 : NestedArithmetic.compile e024=p024 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e023) (NestedArithmetic.compile e013)=p024
  rw [h023,h013]
  exact step024.symm
#print axioms h024
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
