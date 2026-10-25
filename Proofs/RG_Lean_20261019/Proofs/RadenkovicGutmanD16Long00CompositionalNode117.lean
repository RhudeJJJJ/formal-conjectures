/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode112
import Proofs.RadenkovicGutmanD16Long00CompositionalNode116
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e117 : NestedArithmetic.Expr 3 := .plus e112 e116
noncomputable def p117 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,384],[0,384,848]],[[0,0,0],[0,0,0],[0,0,0]],[[0,3456,12672],[3456,14112,17312],[12672,17312,4]],[[0,0,0],[0,0,0],[0,0]],[[162000,310176,176208],[310176,387912,44488],[176208,44488]],[[0,0,0],[0,0,0],[0,0]],[[4843044,4436712,729028],[4436712,1839776,40448],[729028,40448]],[[0,0,0],[0,0,0],[0,0]],[[55423656,24881240,1458688],[24881240,3975560,14768],[1458688,14768]],[[0,0,0],[0,0,0],[0,0]],[[333828780,76258424,1654448],[76258424,4817040,1888],[1654448,1888]],[[0,0,0],[0,0,0],[0,0]],[[1245178616,146830816,1134368],[146830816,3525024,8],[1134368,8]],[[0,0,0],[0,0],[0]],[[3150364852,190566392,478552],[190566392,1587024],[478552]],[[0,0,0],[0,0],[0]],[[5712123312,173153688,121472],[173153688,429640],[121472]],[[0,0,0],[0,0],[0]],[[7685622744,112244432,17072],[112244432,64336],[17072]],[[0,0,0],[0,0],[0]],[[7847521032,52169760,1040],[52169760,4168],[1040]],[[0,0,0],[0,0],[0]],[[6165730048,17246712,4],[17246712,16],[4]],[[0,0],[0]],[[3755210688,3958792],[3958792]],[[0,0],[0]],[[1775932256,600440],[600440]],[[0,0],[0]],[[649603272,54368],[54368]],[[0,0],[0]],[[181861844,2280],[2280]],[[0,0],[0]],[[38226064,8],[8]],[[0]],[[5839608]],[[0]],[[613096]],[[0]],[[39796]],[[0]],[[1240]],[[0]],[[4]]]
theorem step117 : p117=NestedHorner.add p112 p116 := by decide +kernel
#print axioms step117
theorem h117 : NestedArithmetic.compile e117=p117 := StagedExprCompile.compile_plus e117 e112 e116 p112 p116 p117 rfl h112 h116 step117
#print axioms h117
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
