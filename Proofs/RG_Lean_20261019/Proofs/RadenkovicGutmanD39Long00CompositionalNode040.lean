/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode038
import Proofs.RadenkovicGutmanD39Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-37]],[[0,0],[0]],[[369,-333],[-333]],[[0,0],[0]],[[201,-888],[-888]],[[0,0],[0]],[[-5119,-814],[-814]],[[0,0],[0]],[[-17186,-296],[-296]],[[0,0],[0]],[[-26196,-37],[-37]],[[0]],[[-22532]],[[0]],[[-11479]],[[0]],[[-3422]],[[0]],[[-551]],[[0]],[[-37]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
