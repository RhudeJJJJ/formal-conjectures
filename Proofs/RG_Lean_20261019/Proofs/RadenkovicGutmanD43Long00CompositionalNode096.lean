/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode043
import Proofs.RadenkovicGutmanD43Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,5547],[0,5547,-3526]],[[0,0,0],[0,0,0],[0,0]],[[0,49923,49923],[49923,202788,-39431],[49923,-39431]],[[0,0,0],[0,0,0],[0,0]],[[1212084,2024784,63855],[2024784,282252,-139664],[63855,-139664]],[[0,0,0],[0,0,0],[0,0]],[[27850068,11815884,-558054],[11815884,-2141056,-142201],[-558054,-142201]],[[0,0,0],[0,0,0],[0,0]],[[220476222,26255542,-2027579],[26255542,-7952764,-54567],[-2027579,-54567]],[[0,0,0],[0,0,0],[0,0]],[[929160684,10733058,-3055236],[10733058,-12068208,-7052],[-3055236,-7052]],[[0,0,0],[0,0],[0]],[[2423221140,-70933144,-2534205],[-70933144,-10050820],[-2534205]],[[0,0,0],[0,0],[0]],[[4140843584,-183212250,-1236594],[-183212250,-4918512],[-1236594]],[[0,0,0],[0,0],[0]],[[4594997716,-235093427,-353073],[-235093427,-1407476],[-353073]],[[0,0,0],[0,0],[0]],[[2836945726,-191172539,-54567],[-191172539,-217924],[-54567]],[[0,0,0],[0,0],[0]],[[-148535846,-105075703,-3526],[-105075703,-14104],[-3526]],[[0,0],[0]],[[-2319569210,-39653310],[-39653310]],[[0,0],[0]],[[-2676699776,-10143399],[-10143399]],[[0,0],[0]],[[-1837946248,-1682418],[-1682418]],[[0,0],[0]],[[-874576656,-163357],[-163357]],[[0,0],[0]],[[-299899716,-7052],[-7052]],[[0]],[[-74297980]],[[0]],[[-13014466]],[[0]],[[-1531746]],[[0]],[[-108790]],[[0]],[[-3526]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
