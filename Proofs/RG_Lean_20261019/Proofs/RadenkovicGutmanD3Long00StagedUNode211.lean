/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode002
import Proofs.RadenkovicGutmanD3Long00StagedUNode174
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e211 : NestedArithmetic.Expr 3 := .times e002 e174
noncomputable def p211 : NestedHorner.Poly 3 := [[[3],[0]],[[0,0],[0]],[[51,0],[0,0]],[[0,0],[0,0]],[[366,0],[0,0]],[[0,0],[0,0]],[[1443,0],[0,0]],[[0,0],[0,0]],[[3408,0],[0,0]],[[0,0],[0,0]],[[4932,3],[3,0]],[[0,0],[0,0]],[[4290,24],[24,0]],[[0,0],[0,0]],[[2091,66],[66,0]],[[0,0],[0,0]],[[477,72],[72,0]],[[0,0],[0,0]],[[27,27],[27,0]],[[0],[0,0]],[[0],[0,3]]]
theorem step211 : p211=NestedArithmetic.mul p002 p174 := by decide +kernel
#print axioms step211
theorem h211 : NestedArithmetic.compile e211=p211 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e002) (NestedArithmetic.compile e174)=p211
  rw [h002,h174]
  exact step211.symm
#print axioms h211
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
