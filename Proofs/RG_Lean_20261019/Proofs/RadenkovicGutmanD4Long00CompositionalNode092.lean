/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode032
import Proofs.RadenkovicGutmanD4Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .times e032 e063
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,16]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,384],[0,384,8]],[[0,0,0],[0,0,0],[0,0]],[[-1296,-864,2160],[-864,8352,1328],[2160,1328]],[[0,0,0],[0,0,0],[0,0]],[[-36072,32832,13608],[32832,51936,1600],[13608,1600]],[[0,0,0],[0,0,0],[0,0]],[[-162000,331920,35712],[331920,134368,832],[35712,832]],[[0,0,0],[0,0,0],[0,0]],[[336984,1366816,51200],[1366816,190144,192],[51200,192]],[[0,0,0],[0,0,0],[0,0]],[[5387984,3248736,44128],[3248736,162304,16],[44128,16]],[[0,0,0],[0,0],[0]],[[23087576,5035072,23696],[5035072,86784],[23696]],[[0,0,0],[0,0],[0]],[[58572256,5393072,7936],[5393072,29152],[7936]],[[0,0,0],[0,0],[0]],[[102103664,4112032,1600],[4112032,5952],[1600]],[[0,0,0],[0,0],[0]],[[130052288,2260768,176],[2260768,672],[176]],[[0,0,0],[0,0],[0]],[[124925408,896544,8],[896544,32],[8]],[[0,0],[0]],[[92059296,253360],[253360]],[[0,0],[0]],[[52472960,49600],[49600]],[[0,0],[0]],[[23169616,6368],[6368]],[[0,0],[0]],[[7888728,480],[480]],[[0,0],[0]],[[2047392,16],[16]],[[0]],[[396784]],[[0]],[[55472]],[[0]],[[5272]],[[0]],[[304]],[[0]],[[8]]]
theorem step092 : p092=NestedArithmetic.mul p032 p063 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_times e092 e032 e063 p032 p063 p092 rfl h032 h063 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
