/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode043
import Proofs.RadenkovicGutmanD18Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-2916],[0,-5832,1728],[-2916,1728]],[[0,0,0],[0,0,0],[0,0]],[[0,-115668,-9720],[-115668,6480,7488],[-9720,7488]],[[0,0,0],[0,0,0],[0,0]],[[-1078920,-955476,23004],[-955476,218808,9216],[23004,9216]],[[0,0,0],[0,0,0],[0,0]],[[-13131720,-3016764,152280],[-3016764,753264,4032],[152280,4032]],[[0,0,0],[0,0,0],[0,0]],[[-70880184,-3912696,292176],[-3912696,1192608,576],[292176,576]],[[0,0,0],[0,0],[0]],[[-223914240,1327428,285336],[1327428,1047600],[285336]],[[0,0,0],[0,0],[0]],[[-457467840,12549996,157500],[12549996,538488],[157500]],[[0,0,0],[0,0],[0]],[[-623984976,21111408,49608],[21111408,160848],[49608]],[[0,0,0],[0,0],[0]],[[-550349208,20033604,8316],[20033604,25848],[8316]],[[0,0,0],[0,0],[0]],[[-250183224,12309516,576],[12309516,1728],[576]],[[0,0],[0]],[[63434880,5075640],[5075640]],[[0,0],[0]],[[206933400,1398060],[1398060]],[[0,0],[0]],[[182290392,247140],[247140]],[[0,0],[0]],[[99300816,25380],[25380]],[[0,0],[0]],[[37393056,1152],[1152]],[[0]],[[9961920]],[[0]],[[1852920]],[[0]],[[229608]],[[0]],[[17064]],[[0]],[[576]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
