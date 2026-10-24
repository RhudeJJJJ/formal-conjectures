/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode188
import Proofs.RadenkovicGutmanD3Long00StagedUNode174
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e199 : NestedArithmetic.Expr 3 := .times e188 e174
noncomputable def p199 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[37,0],[0,0]],[[0,0],[0,0]],[[295,0],[0,0]],[[0,0],[0,0]],[[1328,0],[0,0]],[[0,0],[0,0]],[[3715,0],[0,0]],[[0,0],[0,0]],[[6696,2],[2,0]],[[0,0],[0,0]],[[7792,19],[19,0]],[[0,0],[0,0]],[[5684,68],[68,0]],[[0,0],[0,0]],[[2409,114],[114,0]],[[0,0],[0,0]],[[495,90],[90,0]],[[0,0],[0,0]],[[27,27],[27,2]],[[0],[0,0]],[[0],[0,3]]]
theorem step199 : p199=NestedArithmetic.mul p188 p174 := by decide +kernel
#print axioms step199
theorem h199 : NestedArithmetic.compile e199=p199 := StagedExprCompile.compile_times e199 e188 e174 p188 p174 p199 rfl h188 h174 step199
#print axioms h199
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
