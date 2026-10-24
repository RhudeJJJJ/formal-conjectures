/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode195
import Proofs.RadenkovicGutmanD5Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[20,0],[0]],[[0,0],[0]],[[300,0],[0]],[[0,0],[0]],[[1880,0],[0]],[[0,0],[0]],[[6380,0],[0]],[[0,0],[0]],[[12720,0],[0]],[[0,0],[0]],[[15140,10],[10]],[[0,0],[0]],[[10440,70],[70]],[[0,0],[0]],[[3780,160],[160]],[[0,0],[0]],[[540,130],[130]],[[0,0],[0]],[[0,30],[30]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
