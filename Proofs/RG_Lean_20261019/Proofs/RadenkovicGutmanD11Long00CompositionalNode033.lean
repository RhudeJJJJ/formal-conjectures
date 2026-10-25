/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode030
import Proofs.RadenkovicGutmanD11Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .times e030 e032
noncomputable def p033 : NestedHorner.Poly 3 := [[[0],[0,11]],[[0,0],[0]],[[-99,99],[99]],[[0,0],[0]],[[33,264],[264]],[[0,0],[0]],[[1837,242],[242]],[[0,0],[0]],[[5654,88],[88]],[[0,0],[0]],[[8316,11],[11]],[[0]],[[6996]],[[0]],[[3509]],[[0]],[[1034]],[[0]],[[165]],[[0]],[[11]]]
theorem step033 : p033=NestedArithmetic.mul p030 p032 := by decide +kernel
#print axioms step033
theorem h033 : NestedArithmetic.compile e033=p033 := StagedExprCompile.compile_times e033 e030 e032 p030 p032 p033 rfl h030 h032 step033
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
