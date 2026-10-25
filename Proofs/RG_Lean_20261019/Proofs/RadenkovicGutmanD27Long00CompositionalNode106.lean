/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode095
import Proofs.RadenkovicGutmanD27Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1944,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-17496,-17496,0],[-17496,-16848,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-460728,-198288,0],[-198288,-57240,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4548960,-962280,0],[-962280,-98928,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-24514488,-2650320,0],[-2650320,-95904,0],[0,0]],[[0,0,0],[0,0],[0]],[[-83777544,-4633416,0],[-4633416,-54000],[0]],[[0,0,0],[0,0],[0]],[[-196447248,-5438880,0],[-5438880,-17496],[0]],[[0,0,0],[0,0],[0]],[[-331232544,-4412016,0],[-4412016,-3024],[0]],[[0,0,0],[0,0],[0]],[[-413593128,-2501280,0],[-2501280,-216],[0]],[[0,0,0],[0,0],[0]],[[-389566800,-987336,0],[-987336,0],[0]],[[0,0],[0]],[[-279740304,-265680],[-265680]],[[0,0],[0]],[[-153771264,-46440],[-46440]],[[0,0],[0]],[[-64569096,-4752],[-4752]],[[0,0],[0]],[[-20523240,-216],[-216]],[[0,0],[0]],[[-4848336,0],[0]],[[0]],[[-824256]],[[0]],[[-95256]],[[0]],[[-6696]],[[0]],[[-216]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
