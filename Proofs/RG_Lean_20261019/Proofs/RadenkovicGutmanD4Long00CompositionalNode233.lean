/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode211
import Proofs.RadenkovicGutmanD4Long00CompositionalNode217
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e233 : NestedArithmetic.Expr 3 := .times e211 e217
noncomputable def p233 : NestedHorner.Poly 3 := [[[16],[0],[0]],[[0,0],[0,0],[0]],[[496,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[7056,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[61056,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[359136,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1520208,32,0],[32,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[4782160,736,0],[736,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[11382912,7552,0],[7552,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[20675904,45600,0],[45600,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[28676800,180000,0],[180000,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[30148400,488112,16],[488112,48,0],[16,0]],[[0,0,0],[0,0,0],[0,0]],[[23605440,930064,240],[930064,736,0],[240,0]],[[0,0,0],[0,0,0],[0,0]],[[13298720,1251424,1504],[1251424,4720,0],[1504,0]],[[0,0,0],[0,0,0],[0,0]],[[5024464,1176176,5104],[1176176,16416,0],[5104,0]],[[0,0,0],[0,0,0],[0,0]],[[1057008,748704,10176],[748704,33600,0],[10176,0]],[[0,0,0],[0,0,0],[0,0]],[[22464,302384,12112],[302384,41120,16],[12112,16]],[[0,0,0],[0,0,0],[0,0]],[[-41040,66816,8352],[66816,29168,112],[8352,112]],[[0,0,0],[0,0,0],[0,0]],[[-6480,4752,3024],[4752,10848,256],[3024,256]],[[0,0,0],[0,0,0],[0,0]],[[0,-432,432],[-432,1584,208],[432,208]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,48],[0,48]]]
theorem step233 : p233=NestedArithmetic.mul p211 p217 := by decide +kernel
#print axioms step233
theorem h233 : NestedArithmetic.compile e233=p233 := StagedExprCompile.compile_times e233 e211 e217 p211 p217 p233 rfl h211 h217 step233
#print axioms h233
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
