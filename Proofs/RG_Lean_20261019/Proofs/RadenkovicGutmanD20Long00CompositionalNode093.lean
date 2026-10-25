/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode033
import Proofs.RadenkovicGutmanD20Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,400]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,9600],[0,9600,40]],[[0,0,0],[0,0,0],[0,0]],[[-32400,-21600,54000],[-21600,208800,30320],[54000,30320]],[[0,0,0],[0,0,0],[0,0]],[[-888840,820800,327240],[820800,1246560,32320],[327240,32320]],[[0,0,0],[0,0,0],[0,0]],[[-3825360,8064720,823680],[8064720,3082720,13760],[823680,13760]],[[0,0,0],[0,0,0],[0,0]],[[9111480,32304160,1124480],[32304160,4131520,2240],[1124480,2240]],[[0,0,0],[0,0,0],[0,0]],[[131435600,74531040,911200],[74531040,3289600,80],[911200,80]],[[0,0,0],[0,0],[0]],[[546081720,111707200,450640],[111707200,1602560],[450640]],[[0,0,0],[0,0],[0]],[[1349473760,115084400,134400],[115084400,472800],[134400]],[[0,0,0],[0,0],[0]],[[2290259760,83769760,22720],[83769760,79680],[22720]],[[0,0,0],[0,0],[0]],[[2833545280,43515680,1840],[43515680,6560],[1840]],[[0,0,0],[0,0],[0]],[[2634461280,16069920,40],[16069920,160],[40]],[[0,0],[0]],[[1870101280,4140400],[4140400]],[[0,0],[0]],[[1020439680,715200],[715200]],[[0,0],[0]],[[427861200,76640],[76640]],[[0,0],[0]],[[136854840,4320],[4320]],[[0,0],[0]],[[32883360,80],[80]],[[0]],[[5779120]],[[0]],[[710320]],[[0]],[[56440]],[[0]],[[2480]],[[0]],[[40]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
