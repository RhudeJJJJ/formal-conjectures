/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode043
import Proofs.RadenkovicGutmanD29Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2523],[0,2523,-1566]],[[0,0,0],[0,0,0],[0,0]],[[0,22707,22707],[22707,92916,-17255],[22707,-17255]],[[0,0,0],[0,0,0],[0,0]],[[554364,927072,32103],[927072,146508,-61712],[32103,-61712]],[[0,0,0],[0,0,0],[0,0]],[[12775428,5498748,-237510],[5498748,-888560,-63017],[-237510,-63017]],[[0,0,0],[0,0,0],[0,0]],[[101710134,12719110,-885515],[12719110,-3435804,-24215],[-885515,-24215]],[[0,0,0],[0,0,0],[0,0]],[[431963004,7387170,-1344324],[7387170,-5274288,-3132],[-1344324,-3132]],[[0,0,0],[0,0],[0]],[[1138818748,-27298280,-1119197],[-27298280,-4418788],[-1119197]],[[0,0,0],[0,0],[0]],[[1979226336,-76770250,-547346],[-76770250,-2170592],[-547346]],[[0,0,0],[0,0],[0]],[[2267744900,-100894915,-156513],[-100894915,-622804],[-156513]],[[0,0,0],[0,0],[0]],[[1533601838,-83008875,-24215],[-83008875,-96628],[-24215]],[[0,0,0],[0,0],[0]],[[184020602,-45950007,-1566],[-45950007,-6264],[-1566]],[[0,0],[0]],[[-855383130,-17425230],[-17425230]],[[0,0],[0]],[[-1094917504,-4473511],[-4473511]],[[0,0],[0]],[[-777660056,-744082],[-744082]],[[0,0],[0]],[[-376367336,-72413],[-72413]],[[0,0],[0]],[[-130391076,-3132],[-3132]],[[0]],[[-32528140]],[[0]],[[-5726514]],[[0]],[[-676570]],[[0]],[[-48198]],[[0]],[[-1566]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
