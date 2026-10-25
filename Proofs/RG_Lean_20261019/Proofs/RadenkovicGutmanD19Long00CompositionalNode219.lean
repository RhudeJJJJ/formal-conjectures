/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode065
import Proofs.RadenkovicGutmanD19Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[19],[0]],[[0,0],[0]],[[304,0],[0]],[[0,0],[0]],[[2033,0],[0]],[[0,0],[0]],[[7372,0],[0]],[[0,0],[0]],[[15732,0],[0]],[[0,0],[0]],[[20064,19],[19]],[[0,0],[0]],[[14801,133],[133]],[[0,0],[0]],[[5700,304],[304]],[[0,0],[0]],[[855,247],[247]],[[0,0],[0]],[[0,57],[57]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
