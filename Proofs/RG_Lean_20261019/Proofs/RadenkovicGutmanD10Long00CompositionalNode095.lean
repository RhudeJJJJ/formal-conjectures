/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode093
import Proofs.RadenkovicGutmanD10Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,100]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-900],[0,-1800,2880],[-900,2880,20]],[[0,0,0],[0,0,0],[0,0]],[[-8100,-30780,10020],[-30780,53880,9840],[10020,9840]],[[0,0,0],[0,0,0],[0,0]],[[-388260,45900,86360],[45900,382840,11120],[86360,11120]],[[0,0,0],[0,0,0],[0,0]],[[-2373300,1884060,247960],[1884060,1030440,5000],[247960,5000]],[[0,0,0],[0,0,0],[0,0]],[[-867900,9595920,367560],[9595920,1467440,880],[367560,880]],[[0,0,0],[0,0,0],[0,0]],[[43030580,24994580,316560],[24994580,1227440,40],[316560,40]],[[0,0,0],[0,0],[0]],[[219070340,40563180,164460],[40563180,624040],[164460]],[[0,0,0],[0,0],[0]],[[592164920,44286200,51240],[44286200,191560],[51240]],[[0,0,0],[0,0],[0]],[[1060553040,33706300,9060],[33706300,33640],[9060]],[[0,0,0],[0,0],[0]],[[1359854880,18140660,780],[18140660,2920],[780]],[[0,0,0],[0,0],[0]],[[1295734080,6896000,20],[6896000,80],[20]],[[0,0],[0]],[[935511080,1820900],[1820900]],[[0,0],[0]],[[516387640,321540],[321540]],[[0,0],[0]],[[218158420,35220],[35220]],[[0,0],[0]],[[70100420,2040],[2040]],[[0,0],[0]],[[16882440,40],[40]],[[0]],[[2968320]],[[0]],[[364380]],[[0]],[[28860]],[[0]],[[1260]],[[0]],[[20]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
