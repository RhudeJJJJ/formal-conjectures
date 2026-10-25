/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode184
import Proofs.RadenkovicGutmanD9Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[9,0],[0]],[[0,0],[0]],[[144,0],[0]],[[0,0],[0]],[[963,0],[0]],[[0,0],[0]],[[3492,0],[0]],[[0,0],[0]],[[7452,0],[0]],[[0,0],[0]],[[9504,9],[9]],[[0,0],[0]],[[7011,63],[63]],[[0,0],[0]],[[2700,144],[144]],[[0,0],[0]],[[405,117],[117]],[[0,0],[0]],[[0,27],[27]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
