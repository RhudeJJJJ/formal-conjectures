/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode043
import Proofs.RadenkovicGutmanD38Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-12996],[0,-25992,8208],[-12996,8208]],[[0,0,0],[0,0,0],[0,0]],[[0,-510948,-38760],[-510948,45600,35568],[-38760,35568]],[[0,0,0],[0,0,0],[0,0]],[[-4740120,-4089636,134444],[-4089636,1089688,43776],[134444,43776]],[[0,0,0],[0,0,0],[0,0]],[[-56860920,-12080124,766840],[-12080124,3665024,19152],[766840,19152]],[[0,0,0],[0,0,0],[0,0]],[[-301360824,-12175656,1430016],[-12175656,5749248,2736],[1430016,2736]],[[0,0,0],[0,0],[0]],[[-929232240,17899748,1379096],[17899748,5023600],[1379096]],[[0,0,0],[0,0],[0]],[[-1832574320,73679036,755820],[73679036,2573208],[755820]],[[0,0,0],[0,0],[0]],[[-2353771376,112050448,236968],[112050448,766688],[236968]],[[0,0,0],[0,0],[0]],[[-1812200088,102028404,39596],[102028404,122968],[39596]],[[0,0,0],[0,0],[0]],[[-398514664,61254556,2736],[61254556,8208],[2736]],[[0,0],[0]],[[891540800,24877080],[24877080]],[[0,0],[0]],[[1319303000,6778060],[6778060]],[[0,0],[0]],[[1011870232,1188260],[1188260]],[[0,0],[0]],[[519518976,121220],[121220]],[[0,0],[0]],[[189242736,5472],[5472]],[[0]],[[49348320]],[[0]],[[9041720]],[[0]],[[1107928]],[[0]],[[81624]],[[0]],[[2736]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
