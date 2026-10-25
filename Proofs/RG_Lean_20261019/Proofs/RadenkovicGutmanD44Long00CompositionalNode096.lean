/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode043
import Proofs.RadenkovicGutmanD44Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,5808],[0,5808,-3696]],[[0,0,0],[0,0,0],[0,0]],[[0,52272,52272],[52272,212256,-41360],[52272,-41360]],[[0,0,0],[0,0,0],[0,0]],[[1268784,2119392,66528],[2119392,293568,-146432],[66528,-146432]],[[0,0,0],[0,0,0],[0,0]],[[29148768,12358368,-586080],[12358368,-2251040,-149072],[-586080,-149072]],[[0,0,0],[0,0,0],[0,0]],[[230695344,27406720,-2126960],[27406720,-8346624,-57200],[-2126960,-57200]],[[0,0,0],[0,0,0],[0,0]],[[971867424,10966560,-3203904],[10966560,-12659328,-7392],[-3203904,-7392]],[[0,0,0],[0,0],[0]],[[2533268848,-74808800,-2657072],[-74808800,-10540288],[-2657072]],[[0,0,0],[0,0],[0]],[[4325297856,-192544000,-1296416],[-192544000,-5157152],[-1296416]],[[0,0,0],[0,0],[0]],[[4791939680,-246809200,-370128],[-246809200,-1475584],[-370128]],[[0,0,0],[0,0],[0]],[[2944069568,-200595120,-57200],[-200595120,-228448],[-57200]],[[0,0,0],[0,0],[0]],[[-182789728,-110219472,-3696],[-110219472,-14784],[-3696]],[[0,0],[0]],[[-2450347680,-41585280],[-41585280]],[[0,0],[0]],[[-2815926784,-10635856],[-10635856]],[[0,0],[0]],[[-1930745696,-1763872],[-1763872]],[[0,0],[0]],[[-918049616,-171248],[-171248]],[[0,0],[0]],[[-314662656,-7392],[-7392]],[[0]],[[-77931040]],[[0]],[[-13647744]],[[0]],[[-1606000]],[[0]],[[-114048]],[[0]],[[-3696]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
