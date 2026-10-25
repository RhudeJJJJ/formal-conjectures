/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode030
import Proofs.RadenkovicGutmanD21Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .times e030 e032
noncomputable def p033 : NestedHorner.Poly 3 := [[[0],[0,21]],[[0,0],[0]],[[-189,189],[189]],[[0,0],[0]],[[63,504],[504]],[[0,0],[0]],[[3507,462],[462]],[[0,0],[0]],[[10794,168],[168]],[[0,0],[0]],[[15876,21],[21]],[[0]],[[13356]],[[0]],[[6699]],[[0]],[[1974]],[[0]],[[315]],[[0]],[[21]]]
theorem step033 : p033=NestedArithmetic.mul p030 p032 := by decide +kernel
#print axioms step033
theorem h033 : NestedArithmetic.compile e033=p033 := StagedExprCompile.compile_times e033 e030 e032 p030 p032 p033 rfl h030 h032 step033
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
