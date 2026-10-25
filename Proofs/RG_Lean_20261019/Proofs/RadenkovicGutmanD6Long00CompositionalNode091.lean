/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode090
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e091 : NestedArithmetic.Expr 3 := .scaled (-1) e090
noncomputable def p091 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,108],[0,108]],[[0,0,0],[0,0,0],[0,0]],[[0,972,1620],[972,5184,504],[1620,504]],[[0,0,0],[0,0,0],[0,0]],[[17496,60588,12744],[60588,39744,732],[12744,732]],[[0,0,0],[0,0,0],[0,0]],[[612360,576072,40140],[576072,122400,444],[40140,444]],[[0,0,0],[0,0,0],[0,0]],[[6391872,2532528,66492],[2532528,200016,120],[66492,120]],[[0,0,0],[0,0,0],[0,0]],[[34592832,6515904,63948],[6515904,191856,12],[63948,12]],[[0,0,0],[0,0],[0]],[[116936136,10861776,37116],[10861776,112464],[37116]],[[0,0,0],[0,0],[0]],[[270450792,12368880,13044],[12368880,40512],[13044]],[[0,0,0],[0,0],[0]],[[450900096,9899724,2676],[9899724,8688],[2676]],[[0,0,0],[0,0],[0]],[[559638408,5641704,288],[5641704,1008],[288]],[[0,0,0],[0,0],[0]],[[527643168,2290536,12],[2290536,48],[12]],[[0,0],[0]],[[382474128,654420],[654420]],[[0,0],[0]],[[214376184,127764],[127764]],[[0,0],[0]],[[92921808,16092],[16092]],[[0,0],[0]],[[30972840,1164],[1164]],[[0,0],[0]],[[7840680,36],[36]],[[0]],[[1474992]],[[0]],[[198888]],[[0]],[[18072]],[[0]],[[984]],[[0]],[[24]]]
theorem step091 : p091=NestedHorner.scale (-1) p090 := by decide +kernel
#print axioms step091
theorem h091 : NestedArithmetic.compile e091=p091 := StagedExprCompile.compile_scaled (-1) e091 e090 p090 p091 rfl h090 step091
#print axioms h091
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
