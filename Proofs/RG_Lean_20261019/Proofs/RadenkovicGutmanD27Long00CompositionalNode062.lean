/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode044
import Proofs.RadenkovicGutmanD27Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,27]],[[0,0],[0,0]],[[243,243],[243,2]],[[0,0],[0]],[[4311,666],[666]],[[0,0],[0]],[[19137,642],[642]],[[0,0],[0]],[[40004,260],[260]],[[0,0],[0]],[[47248,43],[43]],[[0,0],[0]],[[33960,2],[2]],[[0]],[[15259]],[[0]],[[4256]],[[0]],[[703]],[[0]],[[61]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
