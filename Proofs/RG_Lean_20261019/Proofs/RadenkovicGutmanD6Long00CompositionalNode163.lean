/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode160
import Proofs.RadenkovicGutmanD6Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-4],[0]],[[0,0],[0]],[[-56,0],[0,0]],[[0,0],[0,0]],[[-320,0],[0,0]],[[0,0],[0,0]],[[-952,0],[0,0]],[[0,0],[0,0]],[[-1544,0],[0,0]],[[0,0],[0,0]],[[-1248,-4],[-4,0]],[[0,0],[0,0]],[[-224,-32],[-32,0]],[[0,0],[0,0]],[[392,-88],[-88,0]],[[0,0],[0,0]],[[300,-96],[-96,0]],[[0,0],[0,0]],[[72,-36],[-36,0]],[[0],[0,0]],[[0],[0,-4]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
