/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode093
import Proofs.RadenkovicGutmanD8Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,64]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-576],[0,-1152,1824],[-576,1824,16]],[[0,0,0],[0,0,0],[0,0]],[[-5184,-19872,6240],[-19872,33792,6272],[6240,6272]],[[0,0,0],[0,0,0],[0,0]],[[-251856,22464,54320],[22464,241216,7168],[54320,7168]],[[0,0,0],[0,0,0],[0,0]],[[-1600128,1152864,156736],[1152864,651648,3296],[156736,3296]],[[0,0,0],[0,0,0],[0,0]],[[-1254864,5950784,233504],[5950784,932224,608],[233504,608]],[[0,0,0],[0,0,0],[0,0]],[[24274880,15597632,202368],[15597632,784640,32],[202368,32]],[[0,0,0],[0,0],[0]],[[130528560,25434048,106048],[25434048,402560],[106048]],[[0,0,0],[0,0],[0]],[[359272960,27896224,33472],[27896224,125312],[33472]],[[0,0,0],[0,0],[0]],[[649911264,21339040,6048],[21339040,22528],[6048]],[[0,0,0],[0,0],[0]],[[839256192,11553696,544],[11553696,2048],[544]],[[0,0,0],[0,0],[0]],[[804429312,4425568,16],[4425568,64],[16]],[[0,0],[0]],[[584020224,1180640],[1180640]],[[0,0],[0]],[[324201856,211616],[211616]],[[0,0],[0]],[[137819584,23744],[23744]],[[0,0],[0]],[[44607408,1440],[1440]],[[0,0],[0]],[[10839552,32],[32]],[[0]],[[1928416]],[[0]],[[240704]],[[0]],[[19568]],[[0]],[[896]],[[0]],[[16]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
