/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode043
import Proofs.RadenkovicGutmanD3Long00StagedUNode051
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .times e043 e051
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0,3]],[[0,0],[0,0]],[[27,27],[27,2]],[[0,0],[0]],[[495,90],[90]],[[0,0],[0]],[[2409,114],[114]],[[0,0],[0]],[[5684,68],[68]],[[0,0],[0]],[[7792,19],[19]],[[0,0],[0]],[[6696,2],[2]],[[0]],[[3715]],[[0]],[[1328]],[[0]],[[295]],[[0]],[[37]],[[0]],[[2]]]
theorem step061 : p061=NestedArithmetic.mul p043 p051 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_times e061 e043 e051 p043 p051 p061 rfl h043 h051 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
