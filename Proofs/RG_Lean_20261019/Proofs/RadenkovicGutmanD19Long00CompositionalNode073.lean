/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode071
import Proofs.RadenkovicGutmanD19Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-19494,0],[-19494,-4617,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-333963,-372951,0],[-372951,-53352,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6867531,-3014730,0],[-3014730,-251541,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-62465958,-13712015,0],[-13712015,-627684,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-334710669,-39322742,0],[-39322742,-906528,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1186738651,-75473757,0],[-75473757,-786258,0],[0,0]],[[0,0,0],[0,0],[0]],[[-2964551988,-100446122,0],[-100446122,-412053],[0]],[[0,0,0],[0,0],[0]],[[-5423528264,-94676924,0],[-94676924,-127224],[0]],[[0,0,0],[0,0],[0]],[[-7452861891,-63878190,0],[-63878190,-21261],[0]],[[0,0,0],[0,0],[0]],[[-7822449644,-30880871,0],[-30880871,-1482],[0]],[[0,0,0],[0,0],[0]],[[-6336797654,-10589954,0],[-10589954,0],[0]],[[0,0],[0]],[[-3982740708,-2511477],[-2511477]],[[0,0],[0]],[[-1942895483,-391286],[-391286]],[[0,0],[0]],[[-732128843,-36005],[-36005]],[[0,0],[0]],[[-210748380,-1482],[-1482]],[[0,0],[0]],[[-45431660,0],[0]],[[0]],[[-7093061]],[[0]],[[-756827]],[[0]],[[-49343]],[[0]],[[-1482]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
