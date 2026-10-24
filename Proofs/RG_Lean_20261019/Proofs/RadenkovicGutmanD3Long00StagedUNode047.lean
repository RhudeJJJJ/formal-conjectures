/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode046
import Proofs.RadenkovicGutmanD3Long00StagedUNode028
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e047 : NestedArithmetic.Expr 3 := .times e046 e028
noncomputable def p047 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[0,18],[18]],[[0,0],[0]],[[324,78],[78]],[[0,0],[0]],[[2268,96],[96]],[[0,0],[0]],[[6264,42],[42]],[[0,0],[0]],[[9084,6],[6]],[[0]],[[7632]],[[0]],[[3828]],[[0]],[[1128]],[[0]],[[180]],[[0]],[[12]]]
theorem step047 : p047=NestedArithmetic.mul p046 p028 := by decide +kernel
#print axioms step047
theorem h047 : NestedArithmetic.compile e047=p047 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e046) (NestedArithmetic.compile e028)=p047
  rw [h046,h028]
  exact step047.symm
#print axioms h047
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
