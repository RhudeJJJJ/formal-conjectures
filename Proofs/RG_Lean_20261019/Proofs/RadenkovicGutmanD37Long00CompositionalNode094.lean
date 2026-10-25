/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode035
import Proofs.RadenkovicGutmanD37Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-12321],[0,-24642,7770],[-12321,7770]],[[0,0,0],[0,0,0],[0,0]],[[0,-336663,-36852],[-336663,66156,33670],[-36852,33670]],[[0,0,0],[0,0,0],[0,0]],[[-2067930,-1749249,126725],[-1749249,1232470,41440],[126725,41440]],[[0,0,0],[0,0,0],[0,0]],[[-14415570,1588077,724978],[1588077,4153916,18130],[724978,18130]],[[0,0,0],[0,0,0],[0,0]],[[333666,33441710,1352794],[33441710,6626848,2590],[1352794,2590]],[[0,0,0],[0,0],[0]],[[344372616,114628553,1304990],[114628553,5904460],[1304990]],[[0,0,0],[0,0],[0]],[[1746511296,211428767,715321],[211428767,3083062],[715321]],[[0,0,0],[0,0],[0]],[[4764112156,248069016,224294],[248069016,935508],[224294]],[[0,0,0],[0,0],[0]],[[8584551226,196766259,37481],[196766259,152662],[37481]],[[0,0,0],[0,0],[0]],[[11021579758,108042109,2590],[108042109,10360],[2590]],[[0,0],[0]],[[10465244428,41143556],[41143556]],[[0,0],[0]],[[7494571778,10666915],[10666915]],[[0,0],[0]],[[4083939158,1796387],[1796387]],[[0,0],[0]],[[1694244948,177193],[177193]],[[0,0],[0]],[[531057152,7770],[7770]],[[0]],[[123599832]],[[0]],[[20693582]],[[0]],[[2354902]],[[0]],[[163022]],[[0]],[[5180]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
