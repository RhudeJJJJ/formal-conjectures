/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode030
import Proofs.RadenkovicGutmanD40Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .times e030 e032
noncomputable def p033 : NestedHorner.Poly 3 := [[[0],[0,40]],[[0,0],[0]],[[-360,360],[360]],[[0,0],[0]],[[120,960],[960]],[[0,0],[0]],[[6680,880],[880]],[[0,0],[0]],[[20560,320],[320]],[[0,0],[0]],[[30240,40],[40]],[[0]],[[25440]],[[0]],[[12760]],[[0]],[[3760]],[[0]],[[600]],[[0]],[[40]]]
theorem step033 : p033=NestedArithmetic.mul p030 p032 := by decide +kernel
#print axioms step033
theorem h033 : NestedArithmetic.compile e033=p033 := StagedExprCompile.compile_times e033 e030 e032 p030 p032 p033 rfl h030 h032 step033
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
