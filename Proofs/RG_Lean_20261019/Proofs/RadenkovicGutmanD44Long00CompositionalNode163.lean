/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode160
import Proofs.RadenkovicGutmanD44Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-42],[0]],[[0,0],[0]],[[-626,0],[0,0]],[[0,0],[0,0]],[[-3892,0],[0,0]],[[0,0],[0,0]],[[-13074,0],[0,0]],[[0,0],[0,0]],[[-25712,0],[0,0]],[[0,0],[0,0]],[[-29976,-42],[-42,0]],[[0,0],[0,0]],[[-19756,-336],[-336,0]],[[0,0],[0,0]],[[-5954,-924],[-924,0]],[[0,0],[0,0]],[[186,-1008],[-1008,0]],[[0,0],[0,0]],[[414,-378],[-378,0]],[[0],[0,0]],[[0],[0,-42]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
