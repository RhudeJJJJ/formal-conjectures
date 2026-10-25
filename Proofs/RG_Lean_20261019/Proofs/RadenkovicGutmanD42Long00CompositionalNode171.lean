/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode030
import Proofs.RadenkovicGutmanD42Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[84],[0]],[[0,0],[0]],[[1260,0],[0]],[[0,0],[0]],[[7896,0],[0]],[[0,0],[0]],[[26796,0],[0]],[[0,0],[0]],[[53424,0],[0]],[[0,0],[0]],[[63588,42],[42]],[[0,0],[0]],[[43848,294],[294]],[[0,0],[0]],[[15876,672],[672]],[[0,0],[0]],[[2268,546],[546]],[[0,0],[0]],[[0,126],[126]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
