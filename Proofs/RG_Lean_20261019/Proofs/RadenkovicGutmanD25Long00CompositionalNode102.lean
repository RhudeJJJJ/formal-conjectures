/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode100
import Proofs.RadenkovicGutmanD25Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,625]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-5625],[0,-11250,18450],[-5625,18450,50]],[[0,0,0],[0,0,0],[0,0]],[[-50625,-188325,66675],[-188325,354750,62100],[66675,62100]],[[0,0,0],[0,0,0],[0,0]],[[-2331450,465075,562025],[465075,2497450,68300],[562025,68300]],[[0,0,0],[0,0,0],[0,0]],[[-12503025,13199625,1595650],[13199625,6676850,29000],[1595650,29000]],[[0,0,0],[0,0,0],[0,0]],[[15180000,65332800,2337900],[65332800,9425700,4450],[2337900,4450]],[[0,0,0],[0,0,0],[0,0]],[[368155925,168019325,1983900],[168019325,7781900,100],[1983900,100]],[[0,0,0],[0,0],[0]],[[1673553400,270147275,1009275],[270147275,3875850],[1009275]],[[0,0,0],[0,0],[0]],[[4344940150,292300000,304350],[292300000,1149850],[304350]],[[0,0,0],[0,0],[0]],[[7611153650,220210325,50775],[220210325,189650],[50775]],[[0,0,0],[0,0],[0]],[[9609805800,117015275,3825],[117015275,14250],[3825]],[[0,0,0],[0,0],[0]],[[9041247200,43729950,50],[43729950,200],[50]],[[0,0],[0]],[[6450655250,11268875],[11268875]],[[0,0],[0]],[[3517137150,1915975],[1915975]],[[0,0],[0]],[[1465506125,196325],[196325]],[[0,0],[0]],[[463150800,9800],[9800]],[[0,0],[0]],[[109189050,100],[100]],[[0]],[[18642750]],[[0]],[[2189775]],[[0]],[[160850]],[[0]],[[5975]],[[0]],[[50]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
