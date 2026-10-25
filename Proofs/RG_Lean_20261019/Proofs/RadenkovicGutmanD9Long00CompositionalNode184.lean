/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode030
import Proofs.RadenkovicGutmanD9Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[9],[0]],[[0,0],[0]],[[144,0],[0]],[[0,0],[0]],[[963,0],[0]],[[0,0],[0]],[[3492,0],[0]],[[0,0],[0]],[[7452,0],[0]],[[0,0],[0]],[[9504,9],[9]],[[0,0],[0]],[[7011,63],[63]],[[0,0],[0]],[[2700,144],[144]],[[0,0],[0]],[[405,117],[117]],[[0,0],[0]],[[0,27],[27]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
