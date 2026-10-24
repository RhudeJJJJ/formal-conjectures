/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode235
import Proofs.RadenkovicGutmanD5Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e236 : NestedArithmetic.Expr 3 := .times e235 e122
noncomputable def p236 : NestedHorner.Poly 3 := [[[25],[0],[0]],[[0,0],[0,0],[0]],[[775,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[11025,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[95400,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[561150,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2375325,50,0],[50,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[7472125,1150,0],[1150,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[17785800,11800,0],[11800,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[32306100,71250,0],[71250,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[44807500,281250,0],[281250,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[47106875,762675,25],[762675,75,0],[25,0]],[[0,0,0],[0,0,0],[0,0]],[[36883500,1453225,375],[1453225,1150,0],[375,0]],[[0,0,0],[0,0,0],[0,0]],[[20779250,1955350,2350],[1955350,7375,0],[2350,0]],[[0,0,0],[0,0,0],[0,0]],[[7850725,1837775,7975],[1837775,25650,0],[7975,0]],[[0,0,0],[0,0,0],[0,0]],[[1651575,1169850,15900],[1169850,52500,0],[15900,0]],[[0,0,0],[0,0,0],[0,0]],[[35100,472475,18925],[472475,64250,25],[18925,25]],[[0,0,0],[0,0,0],[0,0]],[[-64125,104400,13050],[104400,45575,175],[13050,175]],[[0,0,0],[0,0,0],[0,0]],[[-10125,7425,4725],[7425,16950,400],[4725,400]],[[0,0,0],[0,0,0],[0,0]],[[0,-675,675],[-675,2475,325],[675,325]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,75],[0,75]]]
theorem step236 : p236=NestedArithmetic.mul p235 p122 := by decide +kernel
#print axioms step236
theorem h236 : NestedArithmetic.compile e236=p236 := StagedExprCompile.compile_times e236 e235 e122 p235 p122 p236 rfl h235 h122 step236
#print axioms h236
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
