/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode032
import Proofs.RadenkovicGutmanD4Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e088 : NestedArithmetic.Expr 3 := .times e032 e060
noncomputable def p088 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,48],[0,48,-16]],[[0,0,0],[0,0,0],[0,0]],[[0,-432,432],[-432,1584,-80],[432,-80]],[[0,0,0],[0,0,0],[0,0]],[[-5184,4752,1728],[4752,5664,-512],[1728,-512]],[[0,0,0],[0,0,0],[0,0]],[[-18576,43488,1440],[43488,1520,-592],[1440,-592]],[[0,0,0],[0,0,0],[0,0]],[[91152,115760,-3440],[115760,-21088,-240],[-3440,-240]],[[0,0,0],[0,0,0],[0,0]],[[730608,79968,-9024],[79968,-43200,-32],[-9024,-32]],[[0,0,0],[0,0],[0]],[[1913696,-240784,-9072],[-240784,-40288],[-9072]],[[0,0,0],[0,0],[0]],[[1815456,-722816,-4896],[-722816,-20880],[-4896]],[[0,0,0],[0,0],[0]],[[-2627744,-973040,-1488],[-973040,-6176],[-1488]],[[0,0,0],[0,0],[0]],[[-11627792,-812240,-240],[-812240,-976],[-240]],[[0,0,0],[0,0],[0]],[[-20190592,-454368,-16],[-454368,-64],[-16]],[[0,0],[0]],[[-22462208,-173760],[-173760]],[[0,0],[0]],[[-17755520,-44928],[-44928]],[[0,0],[0]],[[-10355760,-7520],[-7520]],[[0,0],[0]],[[-4516128,-736],[-736]],[[0,0],[0]],[[-1471008,-32],[-32]],[[0]],[[-352992]],[[0]],[[-60592]],[[0]],[[-7040]],[[0]],[[-496]],[[0]],[[-16]]]
theorem step088 : p088=NestedArithmetic.mul p032 p060 := by decide +kernel
#print axioms step088
theorem h088 : NestedArithmetic.compile e088=p088 := StagedExprCompile.compile_times e088 e032 e060 p032 p060 p088 rfl h032 h060 step088
#print axioms h088
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
