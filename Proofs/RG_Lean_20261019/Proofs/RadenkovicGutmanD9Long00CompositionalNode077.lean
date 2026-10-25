/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode076
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e077 : NestedArithmetic.Expr 3 := .scaled (-1) e076
noncomputable def p077 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,729],[0,1458],[729]],[[0,0,0],[0,0],[0]],[[0,24057,6318],[24057,12636],[6318]],[[0,0,0],[0,0],[0]],[[196830,269001,21465],[269001,42930],[21465]],[[0,0,0],[0,0],[0]],[[2690010,1285227,37098],[1285227,74196],[37098]],[[0,0,0],[0,0],[0]],[[16398126,3478950,35964],[3478950,71928],[35964]],[[0,0,0],[0,0],[0]],[[59358096,5971563,20250],[5971563,40500],[20250]],[[0,0,0],[0,0],[0]],[[143256276,6879897,6561],[6879897,13122],[6561]],[[0,0,0],[0,0],[0]],[[245115396,5478516,1134],[5478516,2268],[1134]],[[0,0,0],[0,0],[0]],[[308318886,3050379,81],[3050379,162],[81]],[[0,0],[0]],[[291434598,1183329],[1183329]],[[0,0],[0]],[[209605968,313146],[313146]],[[0,0],[0]],[[115293618,53865],[53865]],[[0,0],[0]],[[48423258,5427],[5427]],[[0,0],[0]],[[15392268,243],[243]],[[0]],[[3636252]],[[0]],[[618192]],[[0]],[[71442]],[[0]],[[5022]],[[0]],[[162]]]
theorem step077 : p077=NestedHorner.scale (-1) p076 := by decide +kernel
#print axioms step077
theorem h077 : NestedArithmetic.compile e077=p077 := StagedExprCompile.compile_scaled (-1) e077 e076 p076 p077 rfl h076 step077
#print axioms h077
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
