/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode038
import Proofs.RadenkovicGutmanD45Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-43]],[[0,0],[0]],[[423,-387],[-387]],[[0,0],[0]],[[183,-1032],[-1032]],[[0,0],[0]],[[-6121,-946],[-946]],[[0,0],[0]],[[-20270,-344],[-344]],[[0,0],[0]],[[-30732,-43],[-43]],[[0]],[[-26348]],[[0]],[[-13393]],[[0]],[[-3986]],[[0]],[[-641]],[[0]],[[-43]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
