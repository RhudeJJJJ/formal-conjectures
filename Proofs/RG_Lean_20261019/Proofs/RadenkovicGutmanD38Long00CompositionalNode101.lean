/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode051
import Proofs.RadenkovicGutmanD38Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1444]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,34656],[0,34656,76]],[[0,0,0],[0,0,0],[0,0]],[[-116964,77976,194940],[77976,781128,108224],[194940,108224]],[[0,0,0],[0,0,0],[0,0]],[[-617652,5236704,1175796],[5236704,4715040,113392],[1175796,113392]],[[0,0,0],[0,0,0],[0,0]],[[28639764,43085160,2943936],[43085160,11816024,46664],[2943936,46664]],[[0,0,0],[0,0,0],[0,0]],[[341741220,164770280,3992888],[164770280,16041168,6992],[3992888,6992]],[[0,0,0],[0,0,0],[0,0]],[[1802197652,373278864,3207352],[373278864,12896896,152],[3207352,152]],[[0,0,0],[0,0],[0]],[[5757343596,553579136,1566208],[553579136,6302832],[1566208]],[[0,0,0],[0,0],[0]],[[12492001288,564818776,457824],[564818776,1843608],[457824]],[[0,0,0],[0,0],[0]],[[19510803448,406394040,74632],[406394040,300656],[74632]],[[0,0,0],[0,0],[0]],[[22681800088,207962600,5548],[207962600,22344],[5548]],[[0,0,0],[0,0],[0]],[[20019031712,75284232,76],[75284232,304],[76]],[[0,0],[0]],[[13561192240,18874600],[18874600]],[[0,0],[0]],[[7079220640,3132416],[3132416]],[[0,0],[0]],[[2841383652,314032],[314032]],[[0,0],[0]],[[868973132,15352],[15352]],[[0,0],[0]],[[198944136,152],[152]],[[0]],[[33072920]],[[0]],[[3788980]],[[0]],[[271548]],[[0]],[[9804]],[[0]],[[76]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
