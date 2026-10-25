/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode204
import Proofs.RadenkovicGutmanD26Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[52,0],[0]],[[0,0],[0]],[[832,0],[0]],[[0,0],[0]],[[5564,0],[0]],[[0,0],[0]],[[20176,0],[0]],[[0,0],[0]],[[43056,0],[0]],[[0,0],[0]],[[54912,52],[52]],[[0,0],[0]],[[40508,364],[364]],[[0,0],[0]],[[15600,832],[832]],[[0,0],[0]],[[2340,676],[676]],[[0,0],[0]],[[0,156],[156]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
