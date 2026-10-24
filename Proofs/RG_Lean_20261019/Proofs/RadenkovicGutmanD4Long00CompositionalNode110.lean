/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e110 : NestedArithmetic.Expr 3 := .pow e050 2
noncomputable def p110 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,16]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-288,480],[0,480,16]],[[0,0,0],[0,0,0],[0,0,0]],[[1296,-4320,3600],[-4320,10752,1984],[3600,1984,4]],[[0,0,0],[0,0,0],[0,0]],[[-33264,39744,26160],[39744,86248,2984],[26160,2984]],[[0,0,0],[0,0,0],[0,0]],[[-75276,663624,79204],[663624,268864,2112],[79204,2112]],[[0,0,0],[0,0,0],[0,0]],[[2855496,3399032,130944],[3399032,453064,752],[130944,752]],[[0,0,0],[0,0,0],[0,0]],[[25689436,9542424,130608],[9542424,461264,128],[130608,128]],[[0,0,0],[0,0,0],[0,0]],[[110127768,17083040,82144],[17083040,297536,8],[82144,8]],[[0,0,0],[0,0],[0]],[[297783572,20861752,33080],[20861752,123504],[33080]],[[0,0,0],[0,0],[0]],[[560951568,17993432,8448],[17993432,32616],[8448]],[[0,0,0],[0,0],[0]],[[773684728,11153744,1312],[11153744,5232],[1312]],[[0,0,0],[0,0],[0]],[[803673352,4996800,112],[4996800,456],[112]],[[0,0,0],[0,0],[0]],[[639154048,1609848,4],[1609848,16],[4]],[[0,0],[0]],[[392567200,366760],[366760]],[[0,0],[0]],[[186716880,57144],[57144]],[[0,0],[0]],[[68585448,5728],[5728]],[[0,0],[0]],[[19291188,328],[328]],[[0,0],[0]],[[4090544,8],[8]],[[0]],[[637480]],[[0]],[[70120]],[[0]],[[5092]],[[0]],[[216]],[[0]],[[4]]]
theorem step110 : p110=NestedArithmetic.power p050 2 := by decide +kernel
#print axioms step110
theorem h110 : NestedArithmetic.compile e110=p110 := StagedExprCompile.compile_pow 2 e110 e050 p050 p110 rfl h050 step110
#print axioms h110
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
