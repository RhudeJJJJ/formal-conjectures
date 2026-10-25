/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode071
import Proofs.RadenkovicGutmanD18Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-17496,0],[-17496,-4212,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-300348,-335340,0],[-335340,-48492,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6179976,-2712852,0],[-2712852,-227916,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-56227284,-12342132,0],[-12342132,-567324,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-301305204,-35393868,0],[-35393868,-817848,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1068260760,-67924044,0],[-67924044,-708408,0],[0,0]],[[0,0,0],[0,0],[0]],[[-2668333716,-90382572,0],[-90382572,-370908],[0]],[[0,0,0],[0,0],[0]],[[-4880999592,-85175712,0],[-85175712,-114444],[0]],[[0,0,0],[0,0],[0]],[[-6706412748,-57457584,0],[-57457584,-19116],[0]],[[0,0,0],[0,0],[0]],[[-7037999748,-27772380,0],[-27772380,-1332],[0]],[[0,0,0],[0,0],[0]],[[-5700552480,-9522540,0],[-9522540,0],[0]],[[0,0],[0]],[[-3582386712,-2258028],[-2258028]],[[0,0],[0]],[[-1747376604,-351756],[-351756]],[[0,0],[0]],[[-658377216,-32364],[-32364]],[[0,0],[0]],[[-189498276,-1332],[-1332]],[[0,0],[0]],[[-40846680,0],[0]],[[0]],[[-6376644]],[[0]],[[-680328]],[[0]],[[-44352]],[[0]],[[-1332]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
