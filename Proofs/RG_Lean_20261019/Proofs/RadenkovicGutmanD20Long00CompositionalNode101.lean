/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode051
import Proofs.RadenkovicGutmanD20Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,400]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,9600],[0,9600,40]],[[0,0,0],[0,0,0],[0,0]],[[-32400,21600,54000],[21600,216720,30320],[54000,30320]],[[0,0,0],[0,0,0],[0,0]],[[-169560,1453680,327240],[1453680,1315200,32320],[327240,32320]],[[0,0,0],[0,0,0],[0,0]],[[7987680,11997360,823680],[11997360,3315920,13760],[823680,13760]],[[0,0,0],[0,0,0],[0,0]],[[95381880,46032560,1124480],[46032560,4534560,2240],[1124480,2240]],[[0,0,0],[0,0,0],[0,0]],[[503911040,104658240,911200],[104658240,3680320,80],[911200,80]],[[0,0,0],[0,0],[0]],[[1613213640,155836880,450640],[155836880,1822560],[450640]],[[0,0,0],[0,0],[0]],[[3508451200,159751600,134400],[159751600,544080],[134400]],[[0,0,0],[0,0],[0]],[[5493831280,115602240,22720],[115602240,92000],[22720]],[[0,0,0],[0,0],[0]],[[6405079120,59586080,1840],[59586080,7440],[1840]],[[0,0,0],[0,0],[0]],[[5671652480,21778800,40],[21778800,160],[40]],[[0,0],[0]],[[3856724800,5534800],[5534800]],[[0,0],[0]],[[2022486400,938000],[938000]],[[0,0],[0]],[[816341280,97600],[97600]],[[0,0],[0]],[[251461640,5200],[5200]],[[0,0],[0]],[[58127040,80],[80]],[[0]],[[9796400]],[[0]],[[1146400]],[[0]],[[85320]],[[0]],[[3360]],[[0]],[[40]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
