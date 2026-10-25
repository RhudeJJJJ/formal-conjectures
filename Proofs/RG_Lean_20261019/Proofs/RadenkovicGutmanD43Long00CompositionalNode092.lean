/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode089
import Proofs.RadenkovicGutmanD43Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,11094],[0,11094,-3526]],[[0,0,0],[0,0,0],[0,0]],[[0,0,133128],[0,449307,-15136],[133128,-15136]],[[0,0,0],[0,0,0],[0,0]],[[435375,3646701,704082],[3646701,2095218,-108962],[704082,-108962]],[[0,0,0],[0,0,0],[0,0]],[[31401567,31595454,1403348],[31595454,3163467,-127882],[1403348,-127882]],[[0,0,0],[0,0,0],[0,0]],[[339669126,119117439,1110690],[119117439,208550,-52116],[1110690,-52116]],[[0,0,0],[0,0,0],[0,0]],[[1770128583,254926188,-172258],[254926188,-4793812,-6966],[-172258,-6966]],[[0,0,0],[0,0],[0]],[[5625137321,337394641,-965178],[337394641,-6171962],[-965178]],[[0,0,0],[0,0],[0]],[[12043472078,277721950,-735816],[277721950,-3692109],[-735816]],[[0,0,0],[0,0],[0]],[[18281709032,126790058,-265482],[126790058,-1191358],[-265482]],[[0,0,0],[0,0],[0]],[[20196449453,8759788,-47730],[8759788,-200165],[-47730]],[[0,0,0],[0,0],[0]],[[16379774742,-27571213,-3440],[-27571213,-13760],[-3440]],[[0,0],[0]],[[9658821078,-18968418],[-18968418]],[[0,0],[0]],[[3971052064,-6501041],[-6501041]],[[0,0],[0]],[[985371617,-1294472],[-1294472]],[[0,0],[0]],[[36035677,-142889],[-142889]],[[0,0],[0]],[[-80433650,-6794],[-6794]],[[0]],[[-35880748]],[[0]],[[-8361909]],[[0]],[[-1174803]],[[0]],[[-94385]],[[0]],[[-3354]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
