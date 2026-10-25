/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode160
import Proofs.RadenkovicGutmanD39Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-37],[0]],[[0,0],[0]],[[-551,0],[0,0]],[[0,0],[0,0]],[[-3422,0],[0,0]],[[0,0],[0,0]],[[-11479,0],[0,0]],[[0,0],[0,0]],[[-22532,0],[0,0]],[[0,0],[0,0]],[[-26196,-37],[-37,0]],[[0,0],[0,0]],[[-17186,-296],[-296,0]],[[0,0],[0,0]],[[-5119,-814],[-814,0]],[[0,0],[0,0]],[[201,-888],[-888,0]],[[0,0],[0,0]],[[369,-333],[-333,0]],[[0],[0,0]],[[0],[0,-37]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
