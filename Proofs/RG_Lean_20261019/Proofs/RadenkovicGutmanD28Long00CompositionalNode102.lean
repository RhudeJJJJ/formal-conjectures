/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode100
import Proofs.RadenkovicGutmanD28Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,784]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-7056],[0,-14112,23184],[-7056,23184,56]],[[0,0,0],[0,0,0],[0,0]],[[-63504,-235872,84000],[-235872,446208,77952],[84000,77952]],[[0,0,0],[0,0,0],[0,0]],[[-2919672,595728,707000],[595728,3138688,85568],[707000,85568]],[[0,0,0],[0,0,0],[0,0]],[[-15570576,16644096,2005696],[16644096,8384768,36176],[2005696,36176]],[[0,0,0],[0,0,0],[0,0]],[[19944456,82233984,2936304],[82233984,11825856,5488],[2936304,5488]],[[0,0,0],[0,0,0],[0,0]],[[465619952,211271312,2489088],[211271312,9751616,112],[2489088,112]],[[0,0,0],[0,0],[0]],[[2109200296,339401552,1264368],[339401552,4848480],[1264368]],[[0,0,0],[0,0],[0]],[[5467242592,366922864,380352],[366922864,1434496],[380352]],[[0,0,0],[0,0],[0]],[[9566780720,276172064,63168],[276172064,235424],[63168]],[[0,0,0],[0,0],[0]],[[12068277984,146590976,4704],[146590976,17472],[4704]],[[0,0,0],[0,0],[0]],[[11345026112,54706512,56],[54706512,224],[56]],[[0,0],[0]],[[8087774240,14070560],[14070560]],[[0,0],[0]],[[4405961952,2385376],[2385376]],[[0,0],[0]],[[1834079408,243152],[243152]],[[0,0],[0]],[[578961768,11984],[11984]],[[0,0],[0]],[[136290336,112],[112]],[[0]],[[23222640]],[[0]],[[2719248]],[[0]],[[198632]],[[0]],[[7280]],[[0]],[[56]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
