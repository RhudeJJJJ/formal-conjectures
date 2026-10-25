/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode033
import Proofs.RadenkovicGutmanD15Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,225]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,5400],[0,5400,30]],[[0,0,0],[0,0,0],[0,0]],[[-18225,-12150,30375],[-12150,117450,17190],[30375,17190]],[[0,0,0],[0,0,0],[0,0]],[[-500580,461700,184680],[461700,703620,18540],[184680,18540]],[[0,0,0],[0,0,0],[0,0]],[[-2162295,4547340,466560],[4547340,1746990,8070],[466560,8070]],[[0,0,0],[0,0,0],[0,0]],[[5093010,18258570,639810],[18258570,2353140,1380],[639810,1380]],[[0,0,0],[0,0,0],[0,0]],[[74085525,42237180,521550],[42237180,1886400,60],[521550,60]],[[0,0,0],[0,0],[0]],[[308629140,63499500,260130],[63499500,928020],[260130]],[[0,0,0],[0,0],[0]],[[764461770,65660400,78600],[65660400,277950],[78600]],[[0,0,0],[0,0],[0]],[[1300567920,48012570,13590],[48012570,48060],[13590]],[[0,0,0],[0,0],[0]],[[1613451810,25087110,1155],[25087110,4170],[1155]],[[0,0,0],[0,0],[0]],[[1504791060,9336690,30],[9336690,120],[30]],[[0,0],[0]],[[1072152960,2431800],[2431800]],[[0,0],[0]],[[587655960,426900],[426900]],[[0,0],[0]],[[247767825,46980],[46980]],[[0,0],[0]],[[79810380,2790],[2790]],[[0,0],[0]],[[19354770,60],[60]],[[0]],[[3444840]],[[0]],[[431265]],[[0]],[[35280]],[[0]],[[1635]],[[0]],[[30]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
