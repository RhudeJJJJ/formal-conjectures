/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode217
import Proofs.RadenkovicGutmanD9Long00CompositionalNode219
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e220 : NestedArithmetic.Expr 3 := .times e217 e219
noncomputable def p220 : NestedHorner.Poly 3 := [[[-162],[0],[0]],[[0,0],[0,0],[0]],[[-5022,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-71442,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-618192,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-3636252,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-15392268,-243,0],[-243,0],[0]],[[0,0,0],[0,0],[0]],[[-48423258,-5427,0],[-5427,0],[0]],[[0,0,0],[0,0],[0]],[[-115293618,-53865,0],[-53865,0],[0]],[[0,0,0],[0,0],[0]],[[-209605968,-313146,0],[-313146,0],[0]],[[0,0,0],[0,0],[0]],[[-291434598,-1183329,0],[-1183329,0],[0]],[[0,0,0],[0,0],[0]],[[-308318886,-3050379,-81],[-3050379,-162],[-81]],[[0,0,0],[0,0],[0]],[[-245115396,-5478516,-1134],[-5478516,-2268],[-1134]],[[0,0,0],[0,0],[0]],[[-143256276,-6879897,-6561],[-6879897,-13122],[-6561]],[[0,0,0],[0,0],[0]],[[-59358096,-5971563,-20250],[-5971563,-40500],[-20250]],[[0,0,0],[0,0],[0]],[[-16398126,-3478950,-35964],[-3478950,-71928],[-35964]],[[0,0,0],[0,0],[0]],[[-2690010,-1285227,-37098],[-1285227,-74196],[-37098]],[[0,0,0],[0,0],[0]],[[-196830,-269001,-21465],[-269001,-42930],[-21465]],[[0,0,0],[0,0],[0]],[[0,-24057,-6318],[-24057,-12636],[-6318]],[[0,0,0],[0,0],[0]],[[0,0,-729],[0,-1458],[-729]]]
theorem step220 : p220=NestedArithmetic.mul p217 p219 := by decide +kernel
#print axioms step220
theorem h220 : NestedArithmetic.compile e220=p220 := StagedExprCompile.compile_times e220 e217 e219 p217 p219 p220 rfl h217 h219 step220
#print axioms h220
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
