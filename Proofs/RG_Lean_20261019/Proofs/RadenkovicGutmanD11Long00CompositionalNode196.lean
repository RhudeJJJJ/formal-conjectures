/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode195
import Proofs.RadenkovicGutmanD11Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[44,0],[0]],[[0,0],[0]],[[660,0],[0]],[[0,0],[0]],[[4136,0],[0]],[[0,0],[0]],[[14036,0],[0]],[[0,0],[0]],[[27984,0],[0]],[[0,0],[0]],[[33308,22],[22]],[[0,0],[0]],[[22968,154],[154]],[[0,0],[0]],[[8316,352],[352]],[[0,0],[0]],[[1188,286],[286]],[[0,0],[0]],[[0,66],[66]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
