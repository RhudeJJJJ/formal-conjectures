/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode043
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e110 : NestedArithmetic.Expr 3 := .pow e043 2
noncomputable def p110 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,1296],[0,2592,-1440],[1296,-1440,400]],[[0,0,0],[0,0,0],[0,0]],[[0,64800,-1728],[64800,-39456,960],[-1728,960]],[[0,0,0],[0,0,0],[0,0]],[[810000,324000,-20160],[324000,-244320,11520],[-20160,11520]],[[0,0,0],[0,0,0],[0,0]],[[9180000,50976,-11808],[50976,-475936,14240],[-11808,14240]],[[0,0,0],[0,0,0],[0,0]],[[46364400,-3289440,89376],[-3289440,-283328,5920],[89376,5920]],[[0,0,0],[0,0,0],[0,0]],[[136135200,-10699392,210720],[-10699392,273600,800],[210720,800]],[[0,0,0],[0,0],[0]],[[252354064,-16648864,212944],[-16648864,548448],[212944]],[[0,0,0],[0,0],[0]],[[293444032,-14008288,116896],[-14008288,372832],[116896]],[[0,0,0],[0,0],[0]],[[179527840,-4672928,36144],[-4672928,128608],[36144]],[[0,0,0],[0,0],[0]],[[-21892640,2675936,5920],[2675936,22560],[5920]],[[0,0,0],[0,0],[0]],[[-150587456,4056448,400],[4056448,1600],[400]],[[0,0],[0]],[[-137571520,2309280],[2309280]],[[0,0],[0]],[[-55102016,758144],[758144]],[[0,0],[0]],[[4248800,149888],[149888]],[[0,0],[0]],[[18267664,16640],[16640]],[[0,0],[0]],[[11282880,800],[800]],[[0]],[[3968160]],[[0]],[[893728]],[[0]],[[128144]],[[0]],[[10720]],[[0]],[[400]]]
theorem step110 : p110=NestedArithmetic.power p043 2 := by decide +kernel
#print axioms step110
theorem h110 : NestedArithmetic.compile e110=p110 := StagedExprCompile.compile_pow 2 e110 e043 p043 p110 rfl h043 step110
#print axioms h110
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
