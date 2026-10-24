/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode096
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .scaled (-1) e096
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,48],[0,48]],[[0,0,0],[0,0,0],[0,0]],[[0,-432,720],[-432,2160,232],[720,232]],[[0,0,0],[0,0,0],[0,0]],[[-6480,14472,5736],[14472,16632,360],[5736,360]],[[0,0,0],[0,0,0],[0,0]],[[39960,181080,18344],[181080,51552,240],[18344,240]],[[0,0,0],[0,0,0],[0,0]],[[1164024,874784,30944],[874784,85016,72],[30944,72]],[[0,0,0],[0,0,0],[0,0]],[[8223888,2372376,30440],[2372376,82576,8],[30440,8]],[[0,0,0],[0,0],[0]],[[31729096,4102960,18192],[4102960,49216],[18192]],[[0,0,0],[0,0],[0]],[[79664184,4810024,6648],[4810024,18112],[6648]],[[0,0,0],[0,0],[0]],[[140676880,3945216,1440],[3945216,3992],[1440]],[[0,0,0],[0,0],[0]],[[182297168,2296808,168],[2296808,480],[168]],[[0,0,0],[0,0],[0]],[[177750904,950344,8],[950344,24],[8]],[[0,0],[0]],[[132322272,276176],[276176]],[[0,0],[0]],[[75738368,54752],[54752]],[[0,0],[0]],[[33359504,6992],[6992]],[[0,0],[0]],[[11246392,512],[512]],[[0,0],[0]],[[2865720,16],[16]],[[0]],[[539760]],[[0]],[[72400]],[[0]],[[6488]],[[0]],[[344]],[[0]],[[8]]]
theorem step097 : p097=NestedHorner.scale (-1) p096 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_scaled (-1) e097 e096 p096 p097 rfl h096 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
