/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode038
import Proofs.RadenkovicGutmanD21Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-19]],[[0,0],[0]],[[207,-171],[-171]],[[0,0],[0]],[[255,-456],[-456]],[[0,0],[0]],[[-2113,-418],[-418]],[[0,0],[0]],[[-7934,-152],[-152]],[[0,0],[0]],[[-12588,-19],[-19]],[[0]],[[-11084]],[[0]],[[-5737]],[[0]],[[-1730]],[[0]],[[-281]],[[0]],[[-19]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
