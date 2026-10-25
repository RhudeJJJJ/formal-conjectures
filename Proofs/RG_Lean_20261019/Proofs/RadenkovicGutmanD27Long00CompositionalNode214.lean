/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode030
import Proofs.RadenkovicGutmanD27Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[27],[0]],[[0,0],[0]],[[459,0],[0,0]],[[0,0],[0,0]],[[3294,0],[0,0]],[[0,0],[0,0]],[[12987,0],[0,0]],[[0,0],[0,0]],[[30672,0],[0,0]],[[0,0],[0,0]],[[44388,27],[27,0]],[[0,0],[0,0]],[[38610,216],[216,0]],[[0,0],[0,0]],[[18819,594],[594,0]],[[0,0],[0,0]],[[4293,648],[648,0]],[[0,0],[0,0]],[[243,243],[243,0]],[[0],[0,0]],[[0],[0,27]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
