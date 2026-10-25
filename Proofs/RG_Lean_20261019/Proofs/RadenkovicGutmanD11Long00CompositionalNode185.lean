/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode184
import Proofs.RadenkovicGutmanD11Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[11,0],[0]],[[0,0],[0]],[[176,0],[0]],[[0,0],[0]],[[1177,0],[0]],[[0,0],[0]],[[4268,0],[0]],[[0,0],[0]],[[9108,0],[0]],[[0,0],[0]],[[11616,11],[11]],[[0,0],[0]],[[8569,77],[77]],[[0,0],[0]],[[3300,176],[176]],[[0,0],[0]],[[495,143],[143]],[[0,0],[0]],[[0,33],[33]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
