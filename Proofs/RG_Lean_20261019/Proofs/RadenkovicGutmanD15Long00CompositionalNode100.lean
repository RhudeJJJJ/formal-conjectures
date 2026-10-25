/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode043
import Proofs.RadenkovicGutmanD15Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-2025],[0,-4050,1170],[-2025,1170]],[[0,0,0],[0,0,0],[0,0]],[[0,-80595,-7020],[-80595,3510,5070],[-7020,5070]],[[0,0,0],[0,0,0],[0,0]],[[-753300,-673515,14085],[-673515,145170,6240],[14085,6240]],[[0,0,0],[0,0,0],[0,0]],[[-9217800,-2175795,100530],[-2175795,504870,2730],[100530,2730]],[[0,0,0],[0,0,0],[0,0]],[[-50083110,-3028740,195330],[-3028740,802500,390],[195330,390]],[[0,0,0],[0,0],[0]],[[-159564150,212265,191790],[212265,706500],[191790]],[[0,0,0],[0,0],[0]],[[-329898990,7664505,106185],[7664505,363690],[106185]],[[0,0,0],[0,0],[0]],[[-458617560,13597200,33510],[13597200,108750],[33510]],[[0,0,0],[0,0],[0]],[[-420116670,13157715,5625],[13157715,17490],[5625]],[[0,0,0],[0,0],[0]],[[-216162660,8169705,390],[8169705,1170],[390]],[[0,0],[0]],[[8003160,3391170],[3391170]],[[0,0],[0]],[[120194550,938475],[938475]],[[0,0],[0]],[[114781590,166485],[166485]],[[0,0],[0]],[[64402290,17145],[17145]],[[0,0],[0]],[[24629850,780],[780]],[[0]],[[6624900]],[[0]],[[1240350]],[[0]],[[154440]],[[0]],[[11520]],[[0]],[[390]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
