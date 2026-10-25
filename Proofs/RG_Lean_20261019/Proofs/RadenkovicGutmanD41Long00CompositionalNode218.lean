/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode034
import Proofs.RadenkovicGutmanD41Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-41],[0]],[[0,0],[0]],[[-656,0],[0]],[[0,0],[0]],[[-4387,0],[0]],[[0,0],[0]],[[-15908,0],[0]],[[0,0],[0]],[[-33948,0],[0]],[[0,0],[0]],[[-43296,-41],[-41]],[[0,0],[0]],[[-31939,-287],[-287]],[[0,0],[0]],[[-12300,-656],[-656]],[[0,0],[0]],[[-1845,-533],[-533]],[[0,0],[0]],[[0,-123],[-123]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
