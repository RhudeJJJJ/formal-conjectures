/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode070
import Proofs.RadenkovicGutmanD11Long00CompositionalNode082
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e083 : NestedArithmetic.Expr 3 := .plus e070 e082
noncomputable def p083 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,264],[0,264,368]],[[0,0,0],[0,0,0],[0,0,0]],[[0,2376,6732],[2376,16920,8032],[6732,8032,4]],[[0,0,0],[0,0,0],[0,0]],[[1296,229500,86568],[229500,259212,20288],[86568,20288]],[[0,0,0],[0,0,0],[0,0]],[[1446768,2895840,350128],[2895840,1103024,18408],[350128,18408]],[[0,0,0],[0,0,0],[0,0]],[[21861684,15229276,693648],[15229276,2255756,6768],[693648,6768]],[[0,0,0],[0,0,0],[0,0]],[[143587812,44746044,782968],[44746044,2621656,888],[782968,888]],[[0,0,0],[0,0,0],[0,0]],[[553767772,83366884,535888],[83366884,1849568,8],[535888,8]],[[0,0,0],[0,0],[0]],[[1420198448,105182216,226292],[105182216,806096],[226292]],[[0,0,0],[0,0],[0]],[[2588666488,93164768,57712],[93164768,212364],[57712]],[[0,0,0],[0,0],[0]],[[3489340000,58995604,8212],[58995604,31232],[8212]],[[0,0,0],[0,0],[0]],[[3564939372,26839412,520],[26839412,2044],[520]],[[0,0,0],[0,0],[0]],[[2802223864,8704452,4],[8704452,16],[4]],[[0,0],[0]],[[1708161488,1966012],[1966012]],[[0,0],[0]],[[809096568,294840],[294840]],[[0,0],[0]],[[296685940,26668],[26668]],[[0,0],[0]],[[83363648,1156],[1156]],[[0,0],[0]],[[17615624,8],[8]],[[0]],[[2712448]],[[0]],[[288436]],[[0]],[[19176]],[[0]],[[636]],[[0]],[[4]]]
theorem step083 : p083=NestedHorner.add p070 p082 := by decide +kernel
#print axioms step083
theorem h083 : NestedArithmetic.compile e083=p083 := StagedExprCompile.compile_plus e083 e070 e082 p070 p082 p083 rfl h070 h082 step083
#print axioms h083
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
