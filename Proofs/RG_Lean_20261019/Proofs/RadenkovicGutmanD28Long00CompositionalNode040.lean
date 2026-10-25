/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode038
import Proofs.RadenkovicGutmanD28Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-26]],[[0,0],[0]],[[270,-234],[-234]],[[0,0],[0]],[[234,-624],[-624]],[[0,0],[0]],[[-3282,-572],[-572]],[[0,0],[0]],[[-11532,-208],[-208]],[[0,0],[0]],[[-17880,-26],[-26]],[[0]],[[-15536]],[[0]],[[-7970]],[[0]],[[-2388]],[[0]],[[-386]],[[0]],[[-26]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
