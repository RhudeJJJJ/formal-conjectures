/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode112
import Proofs.RadenkovicGutmanD6Long00CompositionalNode116
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e117 : NestedArithmetic.Expr 3 := .plus e112 e116
noncomputable def p117 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,144],[0,144,88]],[[0,0,0],[0,0,0],[0,0,0]],[[0,1296,2592],[1296,5472,2352],[2592,2352,4]],[[0,0,0],[0,0,0],[0,0]],[[42120,79056,28728],[79056,72552,5688],[28728,5688]],[[0,0,0],[0,0,0],[0,0]],[[1158084,906552,110628],[906552,298976,5168],[110628,5168]],[[0,0,0],[0,0,0],[0,0]],[[12090816,4606680,214608],[4606680,611400,1968],[214608,1968]],[[0,0,0],[0,0,0],[0,0]],[[68381580,13391064,240288],[13391064,723280,288],[240288,288]],[[0,0,0],[0,0,0],[0,0]],[[244428016,24991136,164608],[24991136,525984,8],[164608,8]],[[0,0,0],[0,0],[0]],[[600380372,31828552,70232],[31828552,238864],[70232]],[[0,0,0],[0,0],[0]],[[1065883232,28613928,18352],[28613928,66440],[18352]],[[0,0,0],[0,0],[0]],[[1412541944,18471792,2752],[18471792,10576],[2752]],[[0,0,0],[0,0],[0]],[[1426820072,8603040,200],[8603040,808],[200]],[[0,0,0],[0,0],[0]],[[1112948448,2870392,4],[2870392,16],[4]],[[0,0],[0]],[[675079008,671672],[671672]],[[0,0],[0]],[[318971136,105640],[105640]],[[0,0],[0]],[[116981952,10288],[10288]],[[0,0],[0]],[[32982964,520],[520]],[[0,0],[0]],[[7025664,8],[8]],[[0]],[[1098328]],[[0]],[[120096]],[[0]],[[8436]],[[0]],[[320]],[[0]],[[4]]]
theorem step117 : p117=NestedHorner.add p112 p116 := by decide +kernel
#print axioms step117
theorem h117 : NestedArithmetic.compile e117=p117 := StagedExprCompile.compile_plus e117 e112 e116 p112 p116 p117 rfl h112 h116 step117
#print axioms h117
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
