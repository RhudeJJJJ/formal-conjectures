/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode218
import Proofs.RadenkovicGutmanD3Long00StagedUNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e218 e003
noncomputable def p219 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[18,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[558,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[7938,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[68688,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[404028,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1710252,27,0],[27,0],[0]],[[0,0,0],[0,0],[0]],[[5380362,603,0],[603,0],[0]],[[0,0,0],[0,0],[0]],[[12810402,5985,0],[5985,0],[0]],[[0,0,0],[0,0],[0]],[[23289552,34794,0],[34794,0],[0]],[[0,0,0],[0,0],[0]],[[32381622,131481,0],[131481,0],[0]],[[0,0,0],[0,0],[0]],[[34257654,338931,9],[338931,18],[9]],[[0,0,0],[0,0],[0]],[[27235044,608724,126],[608724,252],[126]],[[0,0,0],[0,0],[0]],[[15917364,764433,729],[764433,1458],[729]],[[0,0,0],[0,0],[0]],[[6595344,663507,2250],[663507,4500],[2250]],[[0,0,0],[0,0],[0]],[[1822014,386550,3996],[386550,7992],[3996]],[[0,0,0],[0,0],[0]],[[298890,142803,4122],[142803,8244],[4122]],[[0,0,0],[0,0],[0]],[[21870,29889,2385],[29889,4770],[2385]],[[0,0,0],[0,0],[0]],[[0,2673,702],[2673,1404],[702]],[[0,0,0],[0,0],[0]],[[0,0,81],[0,162],[81]]]
theorem step219 : p219=NestedArithmetic.mul p218 p003 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e218 e003 p218 p003 p219 rfl h218 h003 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
