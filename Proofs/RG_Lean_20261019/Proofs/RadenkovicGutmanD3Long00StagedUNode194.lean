/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode190
import Proofs.RadenkovicGutmanD3Long00StagedUNode193
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e194 : NestedArithmetic.Expr 3 := .plus e190 e193
noncomputable def p194 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[45,0],[0,0]],[[0,0],[0,0]],[[413,0],[0,0]],[[0,0],[0,0]],[[2048,0],[0,0]],[[0,0],[0,0]],[[6057,0],[0,0]],[[0,0],[0,0]],[[11052,2],[2,0]],[[0,0],[0,0]],[[12380,25],[25,0]],[[0,0],[0,0]],[[8140,110],[110,0]],[[0,0],[0,0]],[[2775,210],[210,0]],[[0,0],[0,0]],[[315,168],[168,0]],[[0,0],[0,0]],[[-27,45],[45,2]],[[0],[0,0]],[[0],[0,3]]]
theorem step194 : p194=NestedHorner.add p190 p193 := by decide +kernel
#print axioms step194
theorem h194 : NestedArithmetic.compile e194=p194 := by
  change NestedHorner.add (NestedArithmetic.compile e190) (NestedArithmetic.compile e193)=p194
  rw [h190,h193]
  exact step194.symm
#print axioms h194
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
