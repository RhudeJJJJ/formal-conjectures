/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode043
import Proofs.RadenkovicGutmanD18Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,972],[0,972,-576]],[[0,0,0],[0,0,0],[0,0]],[[0,8748,8748],[8748,36288,-6156],[8748,-6156]],[[0,0,0],[0,0,0],[0,0]],[[215784,361584,14580],[361584,69552,-22464],[14580,-22464]],[[0,0,0],[0,0,0],[0,0]],[[4999968,2208384,-79704],[2208384,-280656,-23076],[-79704,-23076]],[[0,0,0],[0,0,0],[0,0]],[[40217472,5461992,-314604],[5461992,-1192464,-8892],[-314604,-8892]],[[0,0,0],[0,0,0],[0,0]],[[173172384,4657608,-485136],[4657608,-1876608,-1152],[-485136,-1152]],[[0,0,0],[0,0],[0]],[[465231240,-6926544,-406980],[-6926544,-1591920],[-406980]],[[0,0,0],[0,0],[0]],[[831785184,-24831000,-199944],[-24831000,-788112],[-199944]],[[0,0,0],[0,0],[0]],[[1002198816,-34506252,-57348],[-34506252,-227376],[-57348]],[[0,0,0],[0,0],[0]],[[766723176,-29127564,-8892],[-29127564,-35424],[-8892]],[[0,0,0],[0,0],[0]],[[252817704,-16370028,-576],[-16370028,-2304],[-576]],[[0,0],[0]],[[-185169960,-6271560],[-6271560]],[[0,0],[0]],[[-333202176,-1622124],[-1622124]],[[0,0],[0]],[[-257431248,-271368],[-271368]],[[0,0],[0]],[[-129504456,-26532],[-26532]],[[0,0],[0]],[[-45884016,-1152],[-1152]],[[0]],[[-11616480]],[[0]],[[-2066616]],[[0]],[[-246096]],[[0]],[[-17640]],[[0]],[[-576]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
