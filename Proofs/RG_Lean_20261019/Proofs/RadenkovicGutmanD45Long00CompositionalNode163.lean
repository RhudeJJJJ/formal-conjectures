/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode160
import Proofs.RadenkovicGutmanD45Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-43],[0]],[[0,0],[0]],[[-641,0],[0,0]],[[0,0],[0,0]],[[-3986,0],[0,0]],[[0,0],[0,0]],[[-13393,0],[0,0]],[[0,0],[0,0]],[[-26348,0],[0,0]],[[0,0],[0,0]],[[-30732,-43],[-43,0]],[[0,0],[0,0]],[[-20270,-344],[-344,0]],[[0,0],[0,0]],[[-6121,-946],[-946,0]],[[0,0],[0,0]],[[183,-1032],[-1032,0]],[[0,0],[0,0]],[[423,-387],[-387,0]],[[0],[0,0]],[[0],[0,-43]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
