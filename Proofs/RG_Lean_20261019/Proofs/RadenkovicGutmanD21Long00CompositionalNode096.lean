/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode043
import Proofs.RadenkovicGutmanD21Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1323],[0,1323,-798]],[[0,0,0],[0,0,0],[0,0]],[[0,11907,11907],[11907,49140,-8631],[11907,-8631]],[[0,0,0],[0,0,0],[0,0]],[[292572,489888,18711],[489888,87948,-31248],[18711,-31248]],[[0,0,0],[0,0,0],[0,0]],[[6765444,2959740,-114534],[2959740,-413616,-32025],[-114534,-32025]],[[0,0,0],[0,0,0],[0,0]],[[54210870,7146342,-441819],[7146342,-1690332,-12327],[-441819,-12327]],[[0,0,0],[0,0,0],[0,0]],[[232243452,5410818,-677124],[5410818,-2633904,-1596],[-677124,-1596]],[[0,0,0],[0,0],[0]],[[619649436,-11268264,-566349],[-11268264,-2223396],[-566349]],[[0,0,0],[0,0],[0]],[[1096638816,-36230250,-277746],[-36230250,-1097376],[-277746]],[[0,0,0],[0,0],[0]],[[1298212356,-49203987,-79569],[-49203987,-315924],[-79569]],[[0,0,0],[0,0],[0]],[[953427342,-41107899,-12327],[-41107899,-49140],[-12327]],[[0,0,0],[0,0],[0]],[[250854618,-22964487,-798],[-22964487,-3192],[-798]],[[0,0],[0]],[[-326045370,-8762670],[-8762670]],[[0,0],[0]],[[-498954624,-2259831],[-2259831]],[[0,0],[0]],[[-372008280,-377202],[-377202]],[[0,0],[0]],[[-184212168,-36813],[-36813]],[[0,0],[0]],[[-64683108,-1596],[-1596]],[[0]],[[-16280460]],[[0]],[[-2884434]],[[0]],[[-342426]],[[0]],[[-24486]],[[0]],[[-798]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
