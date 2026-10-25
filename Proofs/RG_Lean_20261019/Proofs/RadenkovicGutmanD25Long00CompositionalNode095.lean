/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode093
import Proofs.RadenkovicGutmanD25Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,625]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-5625],[0,-11250,18450],[-5625,18450,50]],[[0,0,0],[0,0,0],[0,0]],[[-50625,-188325,66675],[-188325,352950,62100],[66675,62100]],[[0,0,0],[0,0,0],[0,0]],[[-2347650,448875,562025],[448875,2481850,68300],[562025,68300]],[[0,0,0],[0,0,0],[0,0]],[[-12929625,13016025,1595650],[13016025,6623850,29000],[1595650,29000]],[[0,0,0],[0,0,0],[0,0]],[[10968000,64441800,2337900],[64441800,9334100,4450],[2337900,4450]],[[0,0,0],[0,0,0],[0,0]],[[345457325,165565325,1983900],[165565325,7693100,100],[1983900,100]],[[0,0,0],[0,0],[0]],[[1595981600,265857075,1009275],[265857075,3825850],[1009275]],[[0,0,0],[0,0],[0]],[[4163044550,287264000,304350],[287264000,1133650],[304350]],[[0,0,0],[0,0],[0]],[[7304456850,216125125,50775],[216125125,186850],[50775]],[[0,0,0],[0,0],[0]],[[9226849200,114699275,3825],[114699275,14050],[3825]],[[0,0,0],[0,0],[0]],[[8680537200,42815750,50],[42815750,200],[50]],[[0,0],[0]],[[6191636450,11022875],[11022875]],[[0,0],[0]],[[3374756350,1872975],[1872975]],[[0,0],[0]],[[1405719925,191925],[191925]],[[0,0],[0]],[[444147800,9600],[9600]],[[0,0],[0]],[[104699850,100],[100]],[[0]],[[17879550]],[[0]],[[2101575]],[[0]],[[154650]],[[0]],[[5775]],[[0]],[[50]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
