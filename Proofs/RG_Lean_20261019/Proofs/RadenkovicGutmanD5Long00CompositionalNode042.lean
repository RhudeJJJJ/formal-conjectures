/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode030
import Proofs.RadenkovicGutmanD5Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e042 : NestedArithmetic.Expr 3 := .times e030 e028
noncomputable def p042 : NestedHorner.Poly 3 := [[[0],[0]],[[0,15],[15]],[[0,0],[0]],[[270,65],[65]],[[0,0],[0]],[[1890,80],[80]],[[0,0],[0]],[[5220,35],[35]],[[0,0],[0]],[[7570,5],[5]],[[0]],[[6360]],[[0]],[[3190]],[[0]],[[940]],[[0]],[[150]],[[0]],[[10]]]
theorem step042 : p042=NestedArithmetic.mul p030 p028 := by decide +kernel
#print axioms step042
theorem h042 : NestedArithmetic.compile e042=p042 := StagedExprCompile.compile_times e042 e030 e028 p030 p028 p042 rfl h030 h028 step042
#print axioms h042
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
