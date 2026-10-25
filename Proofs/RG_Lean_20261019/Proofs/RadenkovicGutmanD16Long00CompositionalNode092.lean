/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode089
import Proofs.RadenkovicGutmanD16Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1536],[0,1536,-448]],[[0,0,0],[0,0,0],[0,0]],[[0,0,18432],[0,62208,-1312],[18432,-1312]],[[0,0,0],[0,0,0],[0,0]],[[57024,505440,101280],[505440,305280,-12896],[101280,-12896]],[[0,0,0],[0,0,0],[0,0]],[[4300992,4454784,215456],[4454784,522624,-15616],[215456,-15616]],[[0,0,0],[0,0,0],[0,0]],[[47096640,17141760,203328],[17141760,227072,-6432],[203328,-6432]],[[0,0,0],[0,0,0],[0,0]],[[248052480,37690560,39584],[37690560,-409984,-864],[39584,-864]],[[0,0,0],[0,0],[0]],[[797086016,51944512,-85248],[51944512,-660992],[-85248]],[[0,0,0],[0,0],[0]],[[1728632000,45952384,-79392],[45952384,-421248],[-79392]],[[0,0,0],[0,0],[0]],[[2666148224,24977216,-30528],[24977216,-140032],[-30528]],[[0,0,0],[0,0],[0]],[[3008214272,6405280,-5664],[6405280,-23936],[-5664]],[[0,0,0],[0,0],[0]],[[2514286272,-1230688,-416],[-1230688,-1664],[-416]],[[0,0],[0]],[[1554313536,-1715040],[-1715040]],[[0,0],[0]],[[696249280,-678464],[-678464]],[[0,0],[0]],[[212480768,-143840],[-143840]],[[0,0],[0]],[[35312320,-16448],[-16448]],[[0,0],[0]],[[-1942976,-800],[-800]],[[0]],[[-2887936]],[[0]],[[-817920]],[[0]],[[-124800]],[[0]],[[-10496]],[[0]],[[-384]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
