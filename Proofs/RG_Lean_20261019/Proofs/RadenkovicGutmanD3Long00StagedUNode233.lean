/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode232
import Proofs.RadenkovicGutmanD3Long00StagedUNode120
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e233 : NestedArithmetic.Expr 3 := .times e232 e120
noncomputable def p233 : NestedHorner.Poly 3 := [[[9],[0],[0]],[[0,0],[0,0],[0]],[[279,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[3969,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[34344,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[202014,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[855117,18,0],[18,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2689965,414,0],[414,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[6402888,4248,0],[4248,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[11630196,25650,0],[25650,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[16130700,101250,0],[101250,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[16958475,274563,9],[274563,27,0],[9,0]],[[0,0,0],[0,0,0],[0,0]],[[13278060,523161,135],[523161,414,0],[135,0]],[[0,0,0],[0,0,0],[0,0]],[[7480530,703926,846],[703926,2655,0],[846,0]],[[0,0,0],[0,0,0],[0,0]],[[2826261,661599,2871],[661599,9234,0],[2871,0]],[[0,0,0],[0,0,0],[0,0]],[[594567,421146,5724],[421146,18900,0],[5724,0]],[[0,0,0],[0,0,0],[0,0]],[[12636,170091,6813],[170091,23130,9],[6813,9]],[[0,0,0],[0,0,0],[0,0]],[[-23085,37584,4698],[37584,16407,63],[4698,63]],[[0,0,0],[0,0,0],[0,0]],[[-3645,2673,1701],[2673,6102,144],[1701,144]],[[0,0,0],[0,0,0],[0,0]],[[0,-243,243],[-243,891,117],[243,117]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,27],[0,27]]]
theorem step233 : p233=NestedArithmetic.mul p232 p120 := by decide +kernel
#print axioms step233
theorem h233 : NestedArithmetic.compile e233=p233 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e232) (NestedArithmetic.compile e120)=p233
  rw [h232,h120]
  exact step233.symm
#print axioms h233
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
