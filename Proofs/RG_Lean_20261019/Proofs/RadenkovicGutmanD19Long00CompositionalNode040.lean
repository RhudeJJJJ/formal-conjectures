/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode038
import Proofs.RadenkovicGutmanD19Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-17]],[[0,0],[0]],[[189,-153],[-153]],[[0,0],[0]],[[261,-408],[-408]],[[0,0],[0]],[[-1779,-374],[-374]],[[0,0],[0]],[[-6906,-136],[-136]],[[0,0],[0]],[[-11076,-17],[-17]],[[0]],[[-9812]],[[0]],[[-5099]],[[0]],[[-1542]],[[0]],[[-251]],[[0]],[[-17]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
