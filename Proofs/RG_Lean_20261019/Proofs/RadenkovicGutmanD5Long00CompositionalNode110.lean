/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode043
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e110 : NestedArithmetic.Expr 3 := .pow e043 2
noncomputable def p110 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,225],[0,450,-180],[225,-180,36]],[[0,0,0],[0,0,0],[0,0]],[[0,11880,330],[11880,-4092,-132],[330,-132]],[[0,0,0],[0,0,0],[0,0]],[[156816,83592,-1799],[83592,-33550,768],[-1799,768]],[[0,0,0],[0,0,0],[0,0]],[[1976832,194364,-4318],[194364,-84692,1164],[-4318,1164]],[[0,0,0],[0,0,0],[0,0]],[[11249712,-12376,672],[-12376,-96456,516],[672,516]],[[0,0,0],[0,0,0],[0,0]],[[38094096,-988964,11290],[-988964,-41932,72],[11290,72]],[[0,0,0],[0,0],[0]],[[85112836,-2332688,14781],[-2332688,13074],[14781]],[[0,0,0],[0,0],[0]],[[131234600,-2823800,9110],[-2823800,22132],[9110]],[[0,0,0],[0,0],[0]],[[141169492,-2012004,3013],[-2012004,9650],[3013]],[[0,0,0],[0,0],[0]],[[103179048,-793768,516],[-793768,1896],[516]],[[0,0,0],[0,0],[0]],[[45600592,-82540,36],[-82540,144],[36]],[[0,0],[0]],[[5267120,79220],[79220]],[[0,0],[0]],[[-7482500,44620],[44620]],[[0,0],[0]],[[-5392608,10980],[10980]],[[0,0],[0]],[[-1595564,1380],[1380]],[[0,0],[0]],[[-65464,72],[72]],[[0]],[[121660]],[[0]],[[47400]],[[0]],[[8808]],[[0]],[[864]],[[0]],[[36]]]
theorem step110 : p110=NestedArithmetic.power p043 2 := by decide +kernel
#print axioms step110
theorem h110 : NestedArithmetic.compile e110=p110 := StagedExprCompile.compile_pow 2 e110 e043 p043 p110 rfl h043 step110
#print axioms h110
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
