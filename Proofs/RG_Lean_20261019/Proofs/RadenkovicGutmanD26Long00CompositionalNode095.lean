/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode093
import Proofs.RadenkovicGutmanD26Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,676]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-6084],[0,-12168,19968],[-6084,19968,52]],[[0,0,0],[0,0,0],[0,0]],[[-54756,-203580,72228],[-203580,382200,67184],[72228,67184]],[[0,0,0],[0,0,0],[0,0]],[[-2537028,489996,608504],[489996,2686840,73840],[608504,73840]],[[0,0,0],[0,0,0],[0,0]],[[-13931892,14112540,1727128],[14112540,7169448,31304],[1727128,31304]],[[0,0,0],[0,0,0],[0,0]],[[12317604,69824144,2529800],[69824144,10100272,4784],[2529800,4784]],[[0,0,0],[0,0,0],[0,0]],[[375768692,179334740,2145936],[179334740,8321456,104],[2145936,104]],[[0,0,0],[0,0],[0]],[[1732503396,287893164,1091116],[287893164,4135976],[1091116]],[[0,0,0],[0,0],[0]],[[4515562168,310995256,328744],[310995256,1224392],[328744]],[[0,0,0],[0,0],[0]],[[7919248272,233912380,54756],[233912380,201448],[54756]],[[0,0,0],[0,0],[0]],[[9999943200,124095348,4108],[124095348,15080],[4108]],[[0,0,0],[0,0],[0]],[[9405015360,46301632,52],[46301632,208],[52]],[[0,0],[0]],[[6706433448,11912420],[11912420]],[[0,0],[0]],[[3654222520,2022020],[2022020]],[[0,0],[0]],[[1521597844,206804],[206804]],[[0,0],[0]],[[480557220,10296],[10296]],[[0,0],[0]],[[113220744,104],[104]],[[0]],[[19319872]],[[0]],[[2268188]],[[0]],[[166556]],[[0]],[[6188]],[[0]],[[52]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
