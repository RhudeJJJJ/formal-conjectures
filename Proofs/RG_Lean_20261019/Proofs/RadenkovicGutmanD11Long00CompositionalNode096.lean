/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode043
import Proofs.RadenkovicGutmanD11Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,363],[0,363,-198]],[[0,0,0],[0,0,0],[0,0]],[[0,3267,3267],[3267,13860,-1991],[3267,-1991]],[[0,0,0],[0,0,0],[0,0]],[[81972,137808,6831],[137808,34188,-7568],[6831,-7568]],[[0,0,0],[0,0,0],[0,0]],[[1916244,881100,-22374],[881100,-66176,-7865],[-22374,-7865]],[[0,0,0],[0,0,0],[0,0]],[[15666750,2391862,-100859],[2391862,-363132,-3047],[-100859,-3047]],[[0,0,0],[0,0,0],[0,0]],[[68905452,2874498,-160644],[2874498,-603504,-396],[-160644,-396]],[[0,0,0],[0,0],[0]],[[190343956,-337304,-136829],[-337304,-525316],[-136829]],[[0,0,0],[0,0],[0]],[[354040896,-6300250,-67826],[-6300250,-264176],[-67826]],[[0,0,0],[0,0],[0]],[[454812116,-10152307,-19569],[-10152307,-77044],[-19569]],[[0,0,0],[0,0],[0]],[[396543422,-9090939,-3047],[-9090939,-12100],[-3047]],[[0,0,0],[0,0],[0]],[[208398938,-5278647,-198],[-5278647,-792],[-198]],[[0,0],[0]],[[21301830,-2065470],[-2065470]],[[0,0],[0]],[[-68911744,-542311],[-542311]],[[0,0],[0]],[[-69720200,-91762],[-91762]],[[0,0],[0]],[[-38657168,-9053],[-9053]],[[0,0],[0]],[[-14410308,-396],[-396]],[[0]],[[-3764860]],[[0]],[[-684354]],[[0]],[[-82786]],[[0]],[[-6006]],[[0]],[[-198]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
