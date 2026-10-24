/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode030
import Proofs.RadenkovicGutmanD5Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .times e030 e032
noncomputable def p033 : NestedHorner.Poly 3 := [[[0],[0,5]],[[0,0],[0]],[[-45,45],[45]],[[0,0],[0]],[[15,120],[120]],[[0,0],[0]],[[835,110],[110]],[[0,0],[0]],[[2570,40],[40]],[[0,0],[0]],[[3780,5],[5]],[[0]],[[3180]],[[0]],[[1595]],[[0]],[[470]],[[0]],[[75]],[[0]],[[5]]]
theorem step033 : p033=NestedArithmetic.mul p030 p032 := by decide +kernel
#print axioms step033
theorem h033 : NestedArithmetic.compile e033=p033 := StagedExprCompile.compile_times e033 e030 e032 p030 p032 p033 rfl h030 h032 step033
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
