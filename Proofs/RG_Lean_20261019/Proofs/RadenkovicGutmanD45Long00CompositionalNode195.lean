/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode194
import Proofs.RadenkovicGutmanD45Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[180],[0]],[[0,0],[0]],[[2700,0],[0]],[[0,0],[0]],[[16920,0],[0]],[[0,0],[0]],[[57420,0],[0]],[[0,0],[0]],[[114480,0],[0]],[[0,0],[0]],[[136260,90],[90]],[[0,0],[0]],[[93960,630],[630]],[[0,0],[0]],[[34020,1440],[1440]],[[0,0],[0]],[[4860,1170],[1170]],[[0,0],[0]],[[0,270],[270]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
