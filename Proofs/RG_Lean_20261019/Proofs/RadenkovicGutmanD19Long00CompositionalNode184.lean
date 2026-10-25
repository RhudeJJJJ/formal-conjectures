/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode030
import Proofs.RadenkovicGutmanD19Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[19],[0]],[[0,0],[0]],[[304,0],[0]],[[0,0],[0]],[[2033,0],[0]],[[0,0],[0]],[[7372,0],[0]],[[0,0],[0]],[[15732,0],[0]],[[0,0],[0]],[[20064,19],[19]],[[0,0],[0]],[[14801,133],[133]],[[0,0],[0]],[[5700,304],[304]],[[0,0],[0]],[[855,247],[247]],[[0,0],[0]],[[0,57],[57]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
