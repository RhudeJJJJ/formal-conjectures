/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode038
import Proofs.RadenkovicGutmanD44Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-42]],[[0,0],[0]],[[414,-378],[-378]],[[0,0],[0]],[[186,-1008],[-1008]],[[0,0],[0]],[[-5954,-924],[-924]],[[0,0],[0]],[[-19756,-336],[-336]],[[0,0],[0]],[[-29976,-42],[-42]],[[0]],[[-25712]],[[0]],[[-13074]],[[0]],[[-3892]],[[0]],[[-626]],[[0]],[[-42]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
