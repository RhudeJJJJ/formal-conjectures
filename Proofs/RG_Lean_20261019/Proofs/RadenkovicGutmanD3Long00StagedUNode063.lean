/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode061
import Proofs.RadenkovicGutmanD3Long00StagedUNode062
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e063 : NestedArithmetic.Expr 3 := .plus e061 e062
noncomputable def p063 : NestedHorner.Poly 3 := [[[0],[0,3]],[[0,0],[0,0]],[[27,45],[45,2]],[[0,0],[0]],[[765,168],[168]],[[0,0],[0]],[[4209,210],[210]],[[0,0],[0]],[[10358,110],[110]],[[0,0],[0]],[[14128,25],[25]],[[0,0],[0]],[[11664,2],[2]],[[0]],[[6043]],[[0]],[[1970]],[[0]],[[391]],[[0]],[[43]],[[0]],[[2]]]
theorem step063 : p063=NestedHorner.add p061 p062 := by decide +kernel
#print axioms step063
theorem h063 : NestedArithmetic.compile e063=p063 := by
  change NestedHorner.add (NestedArithmetic.compile e061) (NestedArithmetic.compile e062)=p063
  rw [h061,h062]
  exact step063.symm
#print axioms h063
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
