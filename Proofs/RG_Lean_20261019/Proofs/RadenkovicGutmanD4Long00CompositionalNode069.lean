/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode066
import Proofs.RadenkovicGutmanD4Long00CompositionalNode068
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e069 : NestedArithmetic.Expr 3 := .plus e066 e068
noncomputable def p069 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,16]],[[0,0],[0,0,0],[0,0,0]],[[0,0,144],[0,288,384],[144,384,32]],[[0,0,0],[0,0,0],[0,0,0]],[[-1296,5616,3984],[5616,12000,1856],[3984,1856,4]],[[0,0,0],[0,0,0],[0,0]],[[26784,128304,25648],[128304,81560,3240],[25648,3240]],[[0,0,0],[0,0,0],[0,0]],[[903204,992232,76740],[992232,249280,2592],[76740,2592]],[[0,0,0],[0,0,0],[0,0]],[[8668968,4028248,129376],[4028248,427896,976],[129376,976]],[[0,0,0],[0,0,0],[0,0]],[[44705948,10104056,133456],[10104056,451120,160],[133456,160]],[[0,0,0],[0,0,0],[0,0]],[[147807640,16980144,87408],[16980144,303488,8],[87408,8]],[[0,0,0],[0,0],[0]],[[340918500,20004456,36696],[20004456,131376],[36696]],[[0,0,0],[0,0],[0]],[[575832784,16953320,9712],[16953320,35928],[9712]],[[0,0,0],[0,0],[0]],[[734091896,10470848,1536],[10470848,5872],[1536]],[[0,0,0],[0,0],[0]],[[720058776,4726816,128],[4726816,504],[128]],[[0,0,0],[0,0],[0]],[[549891072,1548696,4],[1548696,16],[4]],[[0,0],[0]],[[328960960,361336],[361336]],[[0,0],[0]],[[154353104,57880],[57880]],[[0,0],[0]],[[56603016,5952],[5952]],[[0,0],[0]],[[16077060,344],[344]],[[0,0],[0]],[[3480944,8],[8]],[[0]],[[559880]],[[0]],[[64168]],[[0]],[[4884]],[[0]],[[216]],[[0]],[[4]]]
theorem step069 : p069=NestedHorner.add p066 p068 := by decide +kernel
#print axioms step069
theorem h069 : NestedArithmetic.compile e069=p069 := StagedExprCompile.compile_plus e069 e066 e068 p066 p068 p069 rfl h066 h068 step069
#print axioms h069
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
