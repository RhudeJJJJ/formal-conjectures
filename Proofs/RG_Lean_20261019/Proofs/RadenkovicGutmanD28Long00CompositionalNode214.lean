/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode030
import Proofs.RadenkovicGutmanD28Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[28],[0]],[[0,0],[0]],[[476,0],[0,0]],[[0,0],[0,0]],[[3416,0],[0,0]],[[0,0],[0,0]],[[13468,0],[0,0]],[[0,0],[0,0]],[[31808,0],[0,0]],[[0,0],[0,0]],[[46032,28],[28,0]],[[0,0],[0,0]],[[40040,224],[224,0]],[[0,0],[0,0]],[[19516,616],[616,0]],[[0,0],[0,0]],[[4452,672],[672,0]],[[0,0],[0,0]],[[252,252],[252,0]],[[0],[0,0]],[[0],[0,28]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
