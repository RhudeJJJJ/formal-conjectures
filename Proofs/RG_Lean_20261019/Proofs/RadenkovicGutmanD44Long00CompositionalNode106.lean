/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode095
import Proofs.RadenkovicGutmanD44Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-3168,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-28512,-28512,0],[-28512,-27456,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-750816,-323136,0],[-323136,-93280,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7413120,-1568160,0],[-1568160,-161216,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-39949536,-4319040,0],[-4319040,-156288,0],[0,0]],[[0,0,0],[0,0],[0]],[[-136526368,-7550752,0],[-7550752,-88000],[0]],[[0,0,0],[0,0],[0]],[[-320136256,-8863360,0],[-8863360,-28512],[0]],[[0,0,0],[0,0],[0]],[[-539786368,-7189952,0],[-7189952,-4928],[0]],[[0,0,0],[0,0],[0]],[[-674003616,-4076160,0],[-4076160,-352],[0]],[[0,0,0],[0,0],[0]],[[-634849600,-1608992,0],[-1608992,0],[0]],[[0,0],[0]],[[-455873088,-432960],[-432960]],[[0,0],[0]],[[-250590208,-75680],[-75680]],[[0,0],[0]],[[-105223712,-7744],[-7744]],[[0,0],[0]],[[-33445280,-352],[-352]],[[0,0],[0]],[[-7900992,0],[0]],[[0]],[[-1343232]],[[0]],[[-155232]],[[0]],[[-10912]],[[0]],[[-352]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
