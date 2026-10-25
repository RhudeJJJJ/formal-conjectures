/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode202
import Proofs.RadenkovicGutmanD27Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[61,0],[0,0]],[[0,0],[0,0]],[[703,0],[0,0]],[[0,0],[0,0]],[[4256,0],[0,0]],[[0,0],[0,0]],[[15259,0],[0,0]],[[0,0],[0,0]],[[33960,2],[2,0]],[[0,0],[0,0]],[[47248,43],[43,0]],[[0,0],[0,0]],[[40004,260],[260,0]],[[0,0],[0,0]],[[19137,642],[642,0]],[[0,0],[0,0]],[[4311,666],[666,0]],[[0,0],[0,0]],[[243,243],[243,2]],[[0],[0,0]],[[0],[0,27]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
