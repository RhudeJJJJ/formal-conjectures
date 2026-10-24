/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode051
import Proofs.RadenkovicGutmanD5Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e068 : NestedArithmetic.Expr 3 := .times e051 e066
noncomputable def p068 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,-25]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,-750],[0,-750,-20]],[[0,0,0],[0,0,0],[0,0,0]],[[2025,0,-5625],[0,-20430,-2980],[-5625,-2980,-4]],[[0,0,0],[0,0,0],[0,0]],[[31050,-137700,-40200],[-137700,-142752,-4252],[-40200,-4252]],[[0,0,0],[0,0,0],[0,0]],[[-639549,-1372248,-119524],[-1372248,-416210,-2812],[-119524,-2812]],[[0,0,0],[0,0,0],[0,0]],[[-10041648,-6034446,-193548],[-6034446,-665672,-926],[-193548,-926]],[[0,0,0],[0,0,0],[0,0]],[[-61117133,-15509076,-188318],[-15509076,-645656,-144],[-188318,-144]],[[0,0,0],[0,0,0],[0,0]],[[-218561194,-26008204,-114860],[-26008204,-396612,-8],[-114860,-8]],[[0,0,0],[0,0],[0]],[[-524387994,-30083848,-44504],[-30083848,-156386],[-44504]],[[0,0,0],[0,0],[0]],[[-900952700,-24735700,-10820],[-24735700,-39088],[-10820]],[[0,0,0],[0,0],[0]],[[-1150800978,-14677084,-1577],[-14677084,-5910],[-1577]],[[0,0,0],[0,0],[0]],[[-1118146252,-6310588,-124],[-6310588,-484],[-124]],[[0,0,0],[0,0],[0]],[[-837950628,-1954300,-4],[-1954300,-16],[-4]],[[0,0],[0]],[[-487947480,-428230],[-428230]],[[0,0],[0]],[[-221242205,-64160],[-64160]],[[0,0],[0]],[[-77878258,-6180],[-6180]],[[0,0],[0]],[[-21102554,-340],[-340]],[[0,0],[0]],[[-4334804,-8],[-8]],[[0]],[[-658465]],[[0]],[[-71090]],[[0]],[[-5107]],[[0]],[[-216]],[[0]],[[-4]]]
theorem step068 : p068=NestedArithmetic.mul p051 p066 := by decide +kernel
#print axioms step068
theorem h068 : NestedArithmetic.compile e068=p068 := StagedExprCompile.compile_times e068 e051 e066 p051 p066 p068 rfl h051 h066 step068
#print axioms h068
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
