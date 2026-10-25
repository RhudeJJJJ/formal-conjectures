/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode195
import Proofs.RadenkovicGutmanD21Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[84,0],[0]],[[0,0],[0]],[[1260,0],[0]],[[0,0],[0]],[[7896,0],[0]],[[0,0],[0]],[[26796,0],[0]],[[0,0],[0]],[[53424,0],[0]],[[0,0],[0]],[[63588,42],[42]],[[0,0],[0]],[[43848,294],[294]],[[0,0],[0]],[[15876,672],[672]],[[0,0],[0]],[[2268,546],[546]],[[0,0],[0]],[[0,126],[126]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
