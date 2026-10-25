/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode035
import Proofs.RadenkovicGutmanD8Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-576],[0,-1152,288],[-576,288]],[[0,0,0],[0,0,0],[0,0]],[[0,-16416,-2400],[-16416,384,1248],[-2400,1248]],[[0,0,0],[0,0,0],[0,0]],[[-108864,-108864,1184],[-108864,38656,1536],[1184,1536]],[[0,0,0],[0,0,0],[0,0]],[[-974592,-151488,20800],[-151488,141824,672],[20800,672]],[[0,0,0],[0,0,0],[0,0]],[[-2671488,670144,44256],[670144,233856,96],[44256,96]],[[0,0,0],[0,0],[0]],[[3049344,3271424,45056],[3271424,212224],[45056]],[[0,0,0],[0,0],[0]],[[41289024,6710720,25440],[6710720,112128],[25440]],[[0,0,0],[0,0],[0]],[[136467200,8298176,8128],[8298176,34304],[8128]],[[0,0,0],[0,0],[0]],[[267729792,6794016,1376],[6794016,5632],[1376]],[[0,0,0],[0,0],[0]],[[360823232,3810976,96],[3810976,384],[96]],[[0,0],[0]],[[353595072,1473760],[1473760]],[[0,0],[0]],[[258921152,386560],[386560]],[[0,0],[0]],[[143448448,65696],[65696]],[[0,0],[0]],[[60279040,6528],[6528]],[[0,0],[0]],[[19088832,288],[288]],[[0]],[[4480128]],[[0]],[[755328]],[[0]],[[86464]],[[0]],[[6016]],[[0]],[[192]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
