/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode043
import Proofs.RadenkovicGutmanD29Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-7569],[0,-15138,4698],[-7569,4698]],[[0,0,0],[0,0,0],[0,0]],[[0,-298323,-23316],[-298323,23838,20358],[-23316,20358]],[[0,0,0],[0,0,0],[0,0]],[[-2771820,-2409291,73109],[-2409291,616018,25056],[73109,25056]],[[0,0,0],[0,0,0],[0,0]],[[-33387120,-7257627,432274],[-7257627,2084462,10962],[432274,10962]],[[0,0,0],[0,0,0],[0,0]],[[-177880374,-7947276,812058],[-7947276,3277812,1566],[812058,1566]],[[0,0,0],[0,0],[0]],[[-552370830,8475569,785726],[8475569,2868100],[785726]],[[0,0,0],[0,0],[0]],[[-1100863142,40024553,431433],[40024553,1470474],[431433]],[[0,0,0],[0,0],[0]],[[-1440353672,62337472,135430],[62337472,438422],[135430]],[[0,0,0],[0,0],[0]],[[-1159650318,57349443,22649],[57349443,70354],[22649]],[[0,0,0],[0,0],[0]],[[-348654124,34635193,1566],[34635193,4698],[1566]],[[0,0],[0]],[[420202808,14121666],[14121666]],[[0,0],[0]],[[703786790,3858595],[3858595]],[[0,0],[0]],[[556879750,677933],[677933]],[[0,0],[0]],[[290054346,69281],[69281]],[[0,0],[0]],[[106542114,3132],[3132]],[[0]],[[27935700]],[[0]],[[5138510]],[[0]],[[631504]],[[0]],[[46632]],[[0]],[[1566]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
