/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode184
import Proofs.RadenkovicGutmanD19Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[19,0],[0]],[[0,0],[0]],[[304,0],[0]],[[0,0],[0]],[[2033,0],[0]],[[0,0],[0]],[[7372,0],[0]],[[0,0],[0]],[[15732,0],[0]],[[0,0],[0]],[[20064,19],[19]],[[0,0],[0]],[[14801,133],[133]],[[0,0],[0]],[[5700,304],[304]],[[0,0],[0]],[[855,247],[247]],[[0,0],[0]],[[0,57],[57]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
