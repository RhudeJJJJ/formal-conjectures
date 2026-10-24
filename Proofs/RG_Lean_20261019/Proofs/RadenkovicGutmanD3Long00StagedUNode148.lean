/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode143
import Proofs.RadenkovicGutmanD3Long00StagedUNode147
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e148 : NestedArithmetic.Expr 3 := .plus e143 e147
noncomputable def p148 : NestedHorner.Poly 3 := [[[1]],[[0,0]],[[8,0]],[[0,0]],[[22,0]],[[0,0]],[[24,0]],[[0,0]],[[9,0]],[[0,0]],[[0,1]]]
theorem step148 : p148=NestedHorner.add p143 p147 := by decide +kernel
#print axioms step148
theorem h148 : NestedArithmetic.compile e148=p148 := by
  change NestedHorner.add (NestedArithmetic.compile e143) (NestedArithmetic.compile e147)=p148
  rw [h143,h147]
  exact step148.symm
#print axioms h148
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
