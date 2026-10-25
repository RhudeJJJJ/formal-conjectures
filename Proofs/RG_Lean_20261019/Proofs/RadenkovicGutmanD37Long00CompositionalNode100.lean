/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode043
import Proofs.RadenkovicGutmanD37Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-12321],[0,-24642,7770],[-12321,7770]],[[0,0,0],[0,0,0],[0,0]],[[0,-484515,-36852],[-484515,42846,33670],[-36852,33670]],[[0,0,0],[0,0,0],[0,0]],[[-4495500,-3881115,126725],[-3881115,1030450,41440],[126725,41440]],[[0,0,0],[0,0,0],[0,0]],[[-53946000,-11484171,724978],[-11484171,3467566,18130],[724978,18130]],[[0,0,0],[0,0,0],[0,0]],[[-286043670,-11664620,1352794],[-11664620,5440628,2590],[1352794,2590]],[[0,0,0],[0,0],[0]],[[-882553230,16693697,1304990],[16693697,4754500],[1304990]],[[0,0,0],[0,0],[0]],[[-1742148774,69442969,715321],[69442969,2435562],[715321]],[[0,0,0],[0,0],[0]],[[-2241370312,105816448,224294],[105816448,725718],[224294]],[[0,0,0],[0,0],[0]],[[-1732848750,96435283,37481],[96435283,116402],[37481]],[[0,0,0],[0,0],[0]],[[-394339340,57925609,2590],[57925609,7770],[2590]],[[0,0],[0]],[[831194936,23532962],[23532962]],[[0,0],[0]],[[1241623430,6413395],[6413395]],[[0,0],[0]],[[954715366,1124541],[1124541]],[[0,0],[0]],[[490760970,114737],[114737]],[[0,0],[0]],[[178892706,5180],[5180]],[[0]],[[46671060]],[[0]],[[8554030]],[[0]],[[1048432]],[[0]],[[77256]],[[0]],[[2590]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
