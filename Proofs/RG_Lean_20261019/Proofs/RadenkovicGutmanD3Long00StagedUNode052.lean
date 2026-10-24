/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode002
import Proofs.RadenkovicGutmanD3Long00StagedUNode051
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e052 : NestedArithmetic.Expr 3 := .times e002 e051
noncomputable def p052 : NestedHorner.Poly 3 := [[[0],[0,3]],[[0,0],[0]],[[27,27],[27]],[[0,0],[0]],[[477,72],[72]],[[0,0],[0]],[[2091,66],[66]],[[0,0],[0]],[[4290,24],[24]],[[0,0],[0]],[[4932,3],[3]],[[0]],[[3408]],[[0]],[[1443]],[[0]],[[366]],[[0]],[[51]],[[0]],[[3]]]
theorem step052 : p052=NestedArithmetic.mul p002 p051 := by decide +kernel
#print axioms step052
theorem h052 : NestedArithmetic.compile e052=p052 := StagedExprCompile.compile_times e052 e002 e051 p002 p051 p052 rfl h002 h051 step052
#print axioms h052
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
