/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode213
import Proofs.RadenkovicGutmanD5Long00CompositionalNode219
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e235 : NestedArithmetic.Expr 3 := .times e213 e219
noncomputable def p235 : NestedHorner.Poly 3 := [[[25],[0],[0]],[[0,0],[0,0],[0]],[[775,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[11025,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[95400,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[561150,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2375325,50,0],[50,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[7472125,1150,0],[1150,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[17785800,11800,0],[11800,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[32306100,71250,0],[71250,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[44807500,281250,0],[281250,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[47106875,762675,25],[762675,75,0],[25,0]],[[0,0,0],[0,0,0],[0,0]],[[36883500,1453225,375],[1453225,1150,0],[375,0]],[[0,0,0],[0,0,0],[0,0]],[[20779250,1955350,2350],[1955350,7375,0],[2350,0]],[[0,0,0],[0,0,0],[0,0]],[[7850725,1837775,7975],[1837775,25650,0],[7975,0]],[[0,0,0],[0,0,0],[0,0]],[[1651575,1169850,15900],[1169850,52500,0],[15900,0]],[[0,0,0],[0,0,0],[0,0]],[[35100,472475,18925],[472475,64250,25],[18925,25]],[[0,0,0],[0,0,0],[0,0]],[[-64125,104400,13050],[104400,45575,175],[13050,175]],[[0,0,0],[0,0,0],[0,0]],[[-10125,7425,4725],[7425,16950,400],[4725,400]],[[0,0,0],[0,0,0],[0,0]],[[0,-675,675],[-675,2475,325],[675,325]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,75],[0,75]]]
theorem step235 : p235=NestedArithmetic.mul p213 p219 := by decide +kernel
#print axioms step235
theorem h235 : NestedArithmetic.compile e235=p235 := StagedExprCompile.compile_times e235 e213 e219 p213 p219 p235 rfl h213 h219 step235
#print axioms h235
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
