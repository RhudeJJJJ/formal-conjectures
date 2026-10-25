/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode220
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e221 : NestedArithmetic.Expr 3 := .scaled (-1) e220
noncomputable def p221 : NestedHorner.Poly 3 := [[[162],[0],[0]],[[0,0],[0,0],[0]],[[5022,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[71442,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[618192,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[3636252,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[15392268,243,0],[243,0],[0]],[[0,0,0],[0,0],[0]],[[48423258,5427,0],[5427,0],[0]],[[0,0,0],[0,0],[0]],[[115293618,53865,0],[53865,0],[0]],[[0,0,0],[0,0],[0]],[[209605968,313146,0],[313146,0],[0]],[[0,0,0],[0,0],[0]],[[291434598,1183329,0],[1183329,0],[0]],[[0,0,0],[0,0],[0]],[[308318886,3050379,81],[3050379,162],[81]],[[0,0,0],[0,0],[0]],[[245115396,5478516,1134],[5478516,2268],[1134]],[[0,0,0],[0,0],[0]],[[143256276,6879897,6561],[6879897,13122],[6561]],[[0,0,0],[0,0],[0]],[[59358096,5971563,20250],[5971563,40500],[20250]],[[0,0,0],[0,0],[0]],[[16398126,3478950,35964],[3478950,71928],[35964]],[[0,0,0],[0,0],[0]],[[2690010,1285227,37098],[1285227,74196],[37098]],[[0,0,0],[0,0],[0]],[[196830,269001,21465],[269001,42930],[21465]],[[0,0,0],[0,0],[0]],[[0,24057,6318],[24057,12636],[6318]],[[0,0,0],[0,0],[0]],[[0,0,729],[0,1458],[729]]]
theorem step221 : p221=NestedHorner.scale (-1) p220 := by decide +kernel
#print axioms step221
theorem h221 : NestedArithmetic.compile e221=p221 := StagedExprCompile.compile_scaled (-1) e221 e220 p220 p221 rfl h220 step221
#print axioms h221
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
