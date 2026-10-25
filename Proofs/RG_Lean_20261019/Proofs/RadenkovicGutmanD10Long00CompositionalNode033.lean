/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode030
import Proofs.RadenkovicGutmanD10Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .times e030 e032
noncomputable def p033 : NestedHorner.Poly 3 := [[[0],[0,10]],[[0,0],[0]],[[-90,90],[90]],[[0,0],[0]],[[30,240],[240]],[[0,0],[0]],[[1670,220],[220]],[[0,0],[0]],[[5140,80],[80]],[[0,0],[0]],[[7560,10],[10]],[[0]],[[6360]],[[0]],[[3190]],[[0]],[[940]],[[0]],[[150]],[[0]],[[10]]]
theorem step033 : p033=NestedArithmetic.mul p030 p032 := by decide +kernel
#print axioms step033
theorem h033 : NestedArithmetic.compile e033=p033 := StagedExprCompile.compile_times e033 e030 e032 p030 p032 p033 rfl h030 h032 step033
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
