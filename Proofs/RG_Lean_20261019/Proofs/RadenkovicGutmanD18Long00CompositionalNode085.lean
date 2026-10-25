/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode073
import Proofs.RadenkovicGutmanD18Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-1296,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-11664,-81648,0],[-81648,-23220,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1464804,-1149876,0],[-1149876,-142056,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-21970116,-6926472,0],[-6926472,-418932,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-154129824,-23589900,0],[-23589900,-673992,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-648638964,-50746536,0],[-50746536,-627408,0],[0,0]],[[0,0,0],[0,0],[0]],[[-1823414940,-73108188,0],[-73108188,-344664],[0]],[[0,0,0],[0,0],[0]],[[-3633238008,-72945360,0],[-72945360,-109908],[0]],[[0,0,0],[0,0],[0]],[[-5321980512,-51324264,0],[-51324264,-18792],[0]],[[0,0,0],[0,0],[0]],[[-5866372332,-25608384,0],[-25608384,-1332],[0]],[[0,0,0],[0,0],[0]],[[-4937931000,-8997660,0],[-8997660,0],[0]],[[0,0],[0]],[[-3199623480,-2174760],[-2174760]],[[0,0],[0]],[[-1599727536,-343980],[-343980]],[[0,0],[0]],[[-615039948,-32040],[-32040]],[[0,0],[0]],[[-180001836,-1332],[-1332]],[[0,0],[0]],[[-39343320,0],[0]],[[0]],[[-6214320]],[[0]],[[-669636]],[[0]],[[-44028]],[[0]],[[-1332]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
