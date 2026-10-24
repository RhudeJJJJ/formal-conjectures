/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode032
import Proofs.RadenkovicGutmanD4Long00CompositionalNode073
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .times e032 e073
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,48],[0,48]],[[0,0,0],[0,0,0],[0,0]],[[0,-432,432],[-432,1584,208],[432,208]],[[0,0,0],[0,0,0],[0,0]],[[-6480,4752,3024],[4752,10848,256],[3024,256]],[[0,0,0],[0,0,0],[0,0]],[[-41040,66816,8352],[66816,29168,112],[8352,112]],[[0,0,0],[0,0,0],[0,0]],[[22464,302384,12112],[302384,41120,16],[12112,16]],[[0,0,0],[0,0],[0]],[[1057008,748704,10176],[748704,33600],[10176]],[[0,0,0],[0,0],[0]],[[5024464,1176176,5104],[1176176,16416],[5104]],[[0,0,0],[0,0],[0]],[[13298720,1251424,1504],[1251424,4720],[1504]],[[0,0,0],[0,0],[0]],[[23605440,930064,240],[930064,736],[240]],[[0,0,0],[0,0],[0]],[[30148400,488112,16],[488112,48],[16]],[[0,0],[0]],[[28676800,180000],[180000]],[[0,0],[0]],[[20675904,45600],[45600]],[[0,0],[0]],[[11382912,7552],[7552]],[[0,0],[0]],[[4782160,736],[736]],[[0,0],[0]],[[1520208,32],[32]],[[0]],[[359136]],[[0]],[[61056]],[[0]],[[7056]],[[0]],[[496]],[[0]],[[16]]]
theorem step078 : p078=NestedArithmetic.mul p032 p073 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_times e078 e032 e073 p032 p073 p078 rfl h032 h073 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
