/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode143
import Proofs.RadenkovicGutmanD3Long00StagedUNode145
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e146 : NestedArithmetic.Expr 3 := .plus e143 e145
noncomputable def p146 : NestedHorner.Poly 3 := [[[1],[]],[[0],[0]],[[8],[0]],[[0],[0]],[[22],[0]],[[0],[0]],[[24],[0]],[[0],[0]],[[9],[0]],[[],[0]],[[],[1]]]
theorem step146 : p146=NestedHorner.add p143 p145 := by decide +kernel
#print axioms step146
theorem h146 : NestedArithmetic.compile e146=p146 := by
  change NestedHorner.add (NestedArithmetic.compile e143) (NestedArithmetic.compile e145)=p146
  rw [h143,h145]
  exact step146.symm
#print axioms h146
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
