/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode092
import Proofs.RadenkovicGutmanD7Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-504,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4536,-4536,0],[-4536,-4242,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-118314,-50274,0],[-50274,-13748,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1149498,-236628,0],[-236628,-21938,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6060768,-624750,0],[-624750,-18452,0],[0,0]],[[0,0,0],[0,0],[0]],[[-20131202,-1029476,0],[-1029476,-7784],[0]],[[0,0,0],[0,0],[0]],[[-45500742,-1109766,0],[-1109766,-1036],[0]],[[0,0,0],[0,0],[0]],[[-73142412,-791336,0],[-791336,350],[0]],[[0,0,0],[0,0],[0]],[[-85759072,-362516,0],[-362516,140],[0]],[[0,0,0],[0,0],[0]],[[-74191838,-93856,0],[-93856,14],[0]],[[0,0],[0]],[[-47275564,-4886],[-4886]],[[0,0],[0]],[[-21735308,5180],[5180]],[[0,0],[0]],[[-6773480,1778],[1778]],[[0,0],[0]],[[-1135806,252],[252]],[[0,0],[0]],[[73234,14],[14]],[[0]],[[100548]],[[0]],[[28728]],[[0]],[[4438]],[[0]],[[378]],[[0]],[[14]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
