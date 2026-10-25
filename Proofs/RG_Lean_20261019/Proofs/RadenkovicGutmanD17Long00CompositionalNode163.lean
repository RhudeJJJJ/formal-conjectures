/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode160
import Proofs.RadenkovicGutmanD17Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-15],[0]],[[0,0],[0]],[[-221,0],[0,0]],[[0,0],[0,0]],[[-1354,0],[0,0]],[[0,0],[0,0]],[[-4461,0],[0,0]],[[0,0],[0,0]],[[-8540,0],[0,0]],[[0,0],[0,0]],[[-9564,-15],[-15,0]],[[0,0],[0,0]],[[-5878,-120],[-120,0]],[[0,0],[0,0]],[[-1445,-330],[-330,0]],[[0,0],[0,0]],[[267,-360],[-360,0]],[[0,0],[0,0]],[[171,-135],[-135,0]],[[0],[0,0]],[[0],[0,-15]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
