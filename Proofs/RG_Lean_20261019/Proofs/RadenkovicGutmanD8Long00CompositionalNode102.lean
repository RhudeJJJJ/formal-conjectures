/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode100
import Proofs.RadenkovicGutmanD8Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,64]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-576],[0,-1152,1824],[-576,1824,16]],[[0,0,0],[0,0,0],[0,0]],[[-5184,-19872,6240],[-19872,34368,6272],[6240,6272]],[[0,0,0],[0,0,0],[0,0]],[[-246672,27648,54320],[27648,246208,7168],[54320,7168]],[[0,0,0],[0,0,0],[0,0]],[[-1463616,1211616,156736],[1211616,668608,3296],[156736,3296]],[[0,0,0],[0,0,0],[0,0]],[[92976,6235904,233504],[6235904,961536,608],[233504,608]],[[0,0,0],[0,0,0],[0,0]],[[31538432,16382912,202368],[16382912,813056,32],[202368,32]],[[0,0,0],[0,0],[0]],[[155351536,26806912,106048],[26806912,418560],[106048]],[[0,0,0],[0,0],[0]],[[417479552,29507744,33472],[29507744,130496],[33472]],[[0,0,0],[0,0],[0]],[[748054240,22646304,6048],[22646304,23424],[6048]],[[0,0,0],[0,0],[0]],[[961802304,12294816,544],[12294816,2112],[544]],[[0,0,0],[0,0],[0]],[[919856512,4718112,16],[4718112,64],[16]],[[0,0],[0]],[[666906240,1259360],[1259360]],[[0,0],[0]],[[369763712,225376],[225376]],[[0,0],[0]],[[156951168,25152],[25152]],[[0,0],[0]],[[50688368,1504],[1504]],[[0,0],[0]],[[12276096,32],[32]],[[0]],[[2172640]],[[0]],[[268928]],[[0]],[[21552]],[[0]],[[960]],[[0]],[[16]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
