/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode195
import Proofs.RadenkovicGutmanD26Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[104,0],[0]],[[0,0],[0]],[[1560,0],[0]],[[0,0],[0]],[[9776,0],[0]],[[0,0],[0]],[[33176,0],[0]],[[0,0],[0]],[[66144,0],[0]],[[0,0],[0]],[[78728,52],[52]],[[0,0],[0]],[[54288,364],[364]],[[0,0],[0]],[[19656,832],[832]],[[0,0],[0]],[[2808,676],[676]],[[0,0],[0]],[[0,156],[156]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
