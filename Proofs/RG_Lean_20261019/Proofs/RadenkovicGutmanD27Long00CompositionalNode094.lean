/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode035
import Proofs.RadenkovicGutmanD27Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-6561],[0,-13122,4050],[-6561,4050]],[[0,0,0],[0,0,0],[0,0]],[[0,-180063,-20412],[-180063,32076,17550],[-20412,17550]],[[0,0,0],[0,0,0],[0,0]],[[-1115370,-963009,61965],[-963009,634230,21600],[61965,21600]],[[0,0,0],[0,0,0],[0,0]],[[-8026290,582957,370818],[582957,2151036,9450],[370818,9450]],[[0,0,0],[0,0,0],[0,0]],[[-2949534,16768350,698274],[16768350,3440448,1350],[698274,1350]],[[0,0,0],[0,0],[0]],[[168192936,58611033,676350],[58611033,3069900],[676350]],[[0,0,0],[0,0],[0]],[[883056816,108893727,371601],[108893727,1604502],[371601]],[[0,0,0],[0,0],[0]],[[2436535836,128258856,116694],[128258856,487188],[116694]],[[0,0,0],[0,0],[0]],[[4415845626,101980539,19521],[101980539,79542],[19521]],[[0,0,0],[0,0],[0]],[[5689327518,56089989,1350],[56089989,5400],[1350]],[[0,0],[0]],[[5414932188,21385836],[21385836]],[[0,0],[0]],[[3884476338,5549715],[5549715]],[[0,0],[0]],[[2119470678,935307],[935307]],[[0,0],[0]],[[880168788,92313],[92313]],[[0,0],[0]],[[276113232,4050],[4050]],[[0]],[[64306872]],[[0]],[[10772622]],[[0]],[[1226502]],[[0]],[[84942]],[[0]],[[2700]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
