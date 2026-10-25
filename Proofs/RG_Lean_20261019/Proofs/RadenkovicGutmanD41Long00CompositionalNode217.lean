/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode034
import Proofs.RadenkovicGutmanD41Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-82],[0]],[[0,0],[0]],[[-1230,0],[0]],[[0,0],[0]],[[-7708,0],[0]],[[0,0],[0]],[[-26158,0],[0]],[[0,0],[0]],[[-52152,0],[0]],[[0,0],[0]],[[-62074,-41],[-41]],[[0,0],[0]],[[-42804,-287],[-287]],[[0,0],[0]],[[-15498,-656],[-656]],[[0,0],[0]],[[-2214,-533],[-533]],[[0,0],[0]],[[0,-123],[-123]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
