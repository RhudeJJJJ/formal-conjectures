/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode030
import Proofs.RadenkovicGutmanD40Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,40]],[[0,0],[0]],[[360,360],[360]],[[0,0],[0]],[[6360,960],[960]],[[0,0],[0]],[[27880,880],[880]],[[0,0],[0]],[[57200,320],[320]],[[0,0],[0]],[[65760,40],[40]],[[0]],[[45440]],[[0]],[[19240]],[[0]],[[4880]],[[0]],[[680]],[[0]],[[40]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
