/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode035
import Proofs.RadenkovicGutmanD38Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-12996],[0,-25992,8208],[-12996,8208]],[[0,0,0],[0,0,0],[0,0]],[[0,-354996,-38760],[-354996,70224,35568],[-38760,35568]],[[0,0,0],[0,0,0],[0,0]],[[-2179224,-1840644,134444],[-1840644,1303096,43776],[134444,43776]],[[0,0,0],[0,0,0],[0,0]],[[-15156072,1712052,766840],[1712052,4390064,19152],[766840,19152]],[[0,0,0],[0,0,0],[0,0]],[[792072,35420104,1430016],[35420104,7002336,2736],[1430016,2736]],[[0,0,0],[0,0],[0]],[[365376384,121250324,1379096],[121250324,6238384],[1379096]],[[0,0,0],[0,0],[0]],[[1848803664,223531580,755820],[223531580,3257208],[755820]],[[0,0,0],[0,0],[0]],[[5039239280,262199696,236968],[262199696,988304],[236968]],[[0,0,0],[0,0],[0]],[[9076733352,207939876,39596],[207939876,161272],[39596]],[[0,0,0],[0,0],[0]],[[11650686152,114164236,2736],[114164236,10944],[2736]],[[0,0],[0]],[[11060796192,43471240],[43471240]],[[0,0],[0]],[[7920136472,11269660],[11269660]],[[0,0],[0]],[[4315451608,1897796],[1897796]],[[0,0],[0]],[[1790163280,187188],[187188]],[[0,0],[0]],[[561090672,8208],[8208]],[[0]],[[130583808]],[[0]],[[21862008]],[[0]],[[2487784]],[[0]],[[172216]],[[0]],[[5472]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
