/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode038
import Proofs.RadenkovicGutmanD43Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-41]],[[0,0],[0]],[[405,-369],[-369]],[[0,0],[0]],[[189,-984],[-984]],[[0,0],[0]],[[-5787,-902],[-902]],[[0,0],[0]],[[-19242,-328],[-328]],[[0,0],[0]],[[-29220,-41],[-41]],[[0]],[[-25076]],[[0]],[[-12755]],[[0]],[[-3798]],[[0]],[[-611]],[[0]],[[-41]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
