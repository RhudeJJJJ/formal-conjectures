/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode200
import Proofs.RadenkovicGutmanD3Long00StagedUNode202
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .plus e200 e202
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[43,0],[0,0]],[[0,0],[0,0]],[[391,0],[0,0]],[[0,0],[0,0]],[[1970,0],[0,0]],[[0,0],[0,0]],[[6043,0],[0,0]],[[0,0],[0,0]],[[11664,2],[2,0]],[[0,0],[0,0]],[[14128,25],[25,0]],[[0,0],[0,0]],[[10358,110],[110,0]],[[0,0],[0,0]],[[4209,210],[210,0]],[[0,0],[0,0]],[[765,168],[168,0]],[[0,0],[0,0]],[[27,45],[45,2]],[[0],[0,0]],[[0],[0,3]]]
theorem step203 : p203=NestedHorner.add p200 p202 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := by
  change NestedHorner.add (NestedArithmetic.compile e200) (NestedArithmetic.compile e202)=p203
  rw [h200,h202]
  exact step203.symm
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
