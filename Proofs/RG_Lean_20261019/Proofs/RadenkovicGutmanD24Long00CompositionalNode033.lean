/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode030
import Proofs.RadenkovicGutmanD24Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .times e030 e032
noncomputable def p033 : NestedHorner.Poly 3 := [[[0],[0,24]],[[0,0],[0]],[[-216,216],[216]],[[0,0],[0]],[[72,576],[576]],[[0,0],[0]],[[4008,528],[528]],[[0,0],[0]],[[12336,192],[192]],[[0,0],[0]],[[18144,24],[24]],[[0]],[[15264]],[[0]],[[7656]],[[0]],[[2256]],[[0]],[[360]],[[0]],[[24]]]
theorem step033 : p033=NestedArithmetic.mul p030 p032 := by decide +kernel
#print axioms step033
theorem h033 : NestedArithmetic.compile e033=p033 := StagedExprCompile.compile_times e033 e030 e032 p030 p032 p033 rfl h030 h032 step033
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
