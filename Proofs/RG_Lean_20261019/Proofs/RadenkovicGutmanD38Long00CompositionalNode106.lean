/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode095
import Proofs.RadenkovicGutmanD38Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2736,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-24624,-24624,0],[-24624,-23712,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-648432,-279072,0],[-279072,-80560,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6402240,-1354320,0],[-1354320,-139232,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-34501872,-3730080,0],[-3730080,-134976,0],[0,0]],[[0,0,0],[0,0],[0]],[[-117909136,-6521104,0],[-6521104,-76000],[0]],[[0,0,0],[0,0],[0]],[[-276481312,-7654720,0],[-7654720,-24624],[0]],[[0,0,0],[0,0],[0]],[[-466179136,-6209504,0],[-6209504,-4256],[0]],[[0,0,0],[0,0],[0]],[[-582094032,-3520320,0],[-3520320,-304],[0]],[[0,0,0],[0,0],[0]],[[-548279200,-1389584,0],[-1389584,0],[0]],[[0,0],[0]],[[-393708576,-373920],[-373920]],[[0,0],[0]],[[-216418816,-65360],[-65360]],[[0,0],[0]],[[-90875024,-6688],[-6688]],[[0,0],[0]],[[-28884560,-304],[-304]],[[0,0],[0]],[[-6823584,0],[0]],[[0]],[[-1160064]],[[0]],[[-134064]],[[0]],[[-9424]],[[0]],[[-304]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
