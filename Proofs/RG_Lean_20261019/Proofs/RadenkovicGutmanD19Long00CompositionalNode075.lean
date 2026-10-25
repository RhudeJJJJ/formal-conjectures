/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode033
import Proofs.RadenkovicGutmanD19Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,361]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,6498],[0,6498]],[[0,0,0],[0,0,0],[0,0]],[[-29241,0,29241],[0,116964,17328],[29241,17328]],[[0,0,0],[0,0,0],[0,0]],[[-506844,526338,155952],[526338,623808,15884],[155952,15884]],[[0,0,0],[0,0,0],[0,0]],[[-1549773,4210704,350892],[4210704,1403568,5776],[350892,5776]],[[0,0,0],[0,0,0],[0,0]],[[7364400,15088356,433200],[15088356,1732800,722],[433200,722]],[[0,0,0],[0,0],[0]],[[70186703,31970160,319846],[31970160,1279384],[319846]],[[0,0,0],[0,0],[0]],[[259091144,44543790,144400],[44543790,577600],[144400]],[[0,0,0],[0,0],[0]],[[591886214,42938784,38988],[42938784,155952],[38988]],[[0,0,0],[0,0],[0]],[[942575332,29339192,5776],[29339192,23104],[5776]],[[0,0,0],[0,0],[0]],[[1102570532,14312928,361],[14312928,1444],[361]],[[0,0],[0]],[[973303652,4949310],[4949310]],[[0,0],[0]],[[657435872,1184080],[1184080]],[[0,0],[0]],[[341549320,186276],[186276]],[[0,0],[0]],[[136194831,17328],[17328]],[[0,0],[0]],[[41292624,722],[722]],[[0]],[[9341958]],[[0]],[[1526308]],[[0]],[[170031]],[[0]],[[11552]],[[0]],[[361]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
