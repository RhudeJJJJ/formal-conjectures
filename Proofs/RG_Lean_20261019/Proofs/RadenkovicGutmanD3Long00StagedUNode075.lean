/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .scaled (-1) e074
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,81],[0,162],[81]],[[0,0,0],[0,0],[0]],[[0,2673,702],[2673,1404],[702]],[[0,0,0],[0,0],[0]],[[21870,29889,2385],[29889,4770],[2385]],[[0,0,0],[0,0],[0]],[[298890,142803,4122],[142803,8244],[4122]],[[0,0,0],[0,0],[0]],[[1822014,386550,3996],[386550,7992],[3996]],[[0,0,0],[0,0],[0]],[[6595344,663507,2250],[663507,4500],[2250]],[[0,0,0],[0,0],[0]],[[15917364,764433,729],[764433,1458],[729]],[[0,0,0],[0,0],[0]],[[27235044,608724,126],[608724,252],[126]],[[0,0,0],[0,0],[0]],[[34257654,338931,9],[338931,18],[9]],[[0,0],[0]],[[32381622,131481],[131481]],[[0,0],[0]],[[23289552,34794],[34794]],[[0,0],[0]],[[12810402,5985],[5985]],[[0,0],[0]],[[5380362,603],[603]],[[0,0],[0]],[[1710252,27],[27]],[[0]],[[404028]],[[0]],[[68688]],[[0]],[[7938]],[[0]],[[558]],[[0]],[[18]]]
theorem step075 : p075=NestedHorner.scale (-1) p074 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_scaled (-1) e075 e074 p074 p075 rfl h074 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
