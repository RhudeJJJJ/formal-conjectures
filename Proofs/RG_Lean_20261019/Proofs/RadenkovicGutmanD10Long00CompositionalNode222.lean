/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode221
import Proofs.RadenkovicGutmanD10Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e222 : NestedArithmetic.Expr 3 := .times e221 e003
noncomputable def p222 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[200,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[6200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[88200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[763200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[4489200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[19002800,300,0],[300,0],[0]],[[0,0,0],[0,0],[0]],[[59781800,6700,0],[6700,0],[0]],[[0,0,0],[0,0],[0]],[[142337800,66500,0],[66500,0],[0]],[[0,0,0],[0,0],[0]],[[258772800,386600,0],[386600,0],[0]],[[0,0,0],[0,0],[0]],[[359795800,1460900,0],[1460900,0],[0]],[[0,0,0],[0,0],[0]],[[380640600,3765900,100],[3765900,200],[100]],[[0,0,0],[0,0],[0]],[[302611600,6763600,1400],[6763600,2800],[1400]],[[0,0,0],[0,0],[0]],[[176859600,8493700,8100],[8493700,16200],[8100]],[[0,0,0],[0,0],[0]],[[73281600,7372300,25000],[7372300,50000],[25000]],[[0,0,0],[0,0],[0]],[[20244600,4295000,44400],[4295000,88800],[44400]],[[0,0,0],[0,0],[0]],[[3321000,1586700,45800],[1586700,91600],[45800]],[[0,0,0],[0,0],[0]],[[243000,332100,26500],[332100,53000],[26500]],[[0,0,0],[0,0],[0]],[[0,29700,7800],[29700,15600],[7800]],[[0,0,0],[0,0],[0]],[[0,0,900],[0,1800],[900]]]
theorem step222 : p222=NestedArithmetic.mul p221 p003 := by decide +kernel
#print axioms step222
theorem h222 : NestedArithmetic.compile e222=p222 := StagedExprCompile.compile_times e222 e221 e003 p221 p003 p222 rfl h221 h003 step222
#print axioms h222
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
