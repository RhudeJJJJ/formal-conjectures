/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode089
import Proofs.RadenkovicGutmanD30Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,5400],[0,5400,-1680]],[[0,0,0],[0,0,0],[0,0]],[[0,0,64800],[0,218700,-6660],[64800,-6660]],[[0,0,0],[0,0,0],[0,0]],[[208980,1775520,346140],[1775520,1033560,-51060],[346140,-51060]],[[0,0,0],[0,0,0],[0,0]],[[15242580,15451560,702180],[15451560,1616220,-60360],[702180,-60360]],[[0,0,0],[0,0,0],[0,0]],[[165395520,58566780,585360],[58566780,280440,-24660],[585360,-24660]],[[0,0,0],[0,0,0],[0,0]],[[864292860,126247560,-26580],[126247560,-2104320,-3300],[-26580,-3300]],[[0,0,0],[0,0],[0]],[[2754524940,168949260,-426120],[168949260,-2829480],[-426120]],[[0,0,0],[0,0],[0]],[[5917382160,141952680,-337860],[141952680,-1715940],[-337860]],[[0,0,0],[0,0],[0]],[[9020477520,68416080,-123600],[68416080,-557400],[-123600]],[[0,0,0],[0,0],[0]],[[10021958100,8951460,-22380],[8951460,-94020],[-22380]],[[0,0,0],[0,0],[0]],[[8195341680,-11085120,-1620],[-11085120,-6480],[-1620]],[[0,0],[0]],[[4897346880,-8410260],[-8410260]],[[0,0],[0]],[[2065114680,-2964300],[-2964300]],[[0,0],[0]],[[548288100,-598140],[-598140]],[[0,0],[0]],[[44915340,-66540],[-66540]],[[0,0],[0]],[[-30851520,-3180],[-3180]],[[0]],[[-15587280]],[[0]],[[-3763380]],[[0]],[[-537660]],[[0]],[[-43620]],[[0]],[[-1560]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
