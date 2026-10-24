/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode117
import Proofs.RadenkovicGutmanD2Long00CompositionalNode036
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e117 e036
noncomputable def p172 : NestedHorner.Poly 3 := [[[0]]]
theorem step172 : p172=NestedArithmetic.mul p117 p036 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e117 e036 p117 p036 p172 rfl h117 h036 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
