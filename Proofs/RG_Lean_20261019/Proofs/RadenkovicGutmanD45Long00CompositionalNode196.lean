/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode195
import Proofs.RadenkovicGutmanD45Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[180,0],[0]],[[0,0],[0]],[[2700,0],[0]],[[0,0],[0]],[[16920,0],[0]],[[0,0],[0]],[[57420,0],[0]],[[0,0],[0]],[[114480,0],[0]],[[0,0],[0]],[[136260,90],[90]],[[0,0],[0]],[[93960,630],[630]],[[0,0],[0]],[[34020,1440],[1440]],[[0,0],[0]],[[4860,1170],[1170]],[[0,0],[0]],[[0,270],[270]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
