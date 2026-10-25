/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode071
import Proofs.RadenkovicGutmanD33Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-58806,0],[-58806,-12177,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-991683,-1109295,0],[-1109295,-145332,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-20297871,-8911782,0],[-8911782,-703461,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-184235634,-40452687,0],[-40452687,-1791504,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-986593509,-116018298,0],[-116018298,-2626008,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3498972015,-222906189,0],[-222906189,-2301618,0],[0,0]],[[0,0,0],[0,0],[0]],[[-8747148696,-297066462,0],[-297066462,-1215093],[0]],[[0,0,0],[0,0],[0]],[[-16018194192,-280406412,0],[-280406412,-377124],[0]],[[0,0,0],[0,0],[0]],[[-22035404523,-189450294,0],[-189450294,-63261],[0]],[[0,0,0],[0,0],[0]],[[-23153405088,-91703535,0],[-91703535,-4422],[0]],[[0,0,0],[0,0],[0]],[[-18776074350,-31484310,0],[-31484310,0],[0]],[[0,0],[0]],[[-11812950732,-7474533],[-7474533]],[[0,0],[0]],[[-5768207379,-1165626],[-1165626]],[[0,0],[0]],[[-2175534471,-107349],[-107349]],[[0,0],[0]],[[-626760816,-4422],[-4422]],[[0,0],[0]],[[-135216180,0],[0]],[[0]],[[-21125709]],[[0]],[[-2255583]],[[0]],[[-147147]],[[0]],[[-4422]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
