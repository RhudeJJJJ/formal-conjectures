/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode194
import Proofs.RadenkovicGutmanD42Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[168],[0]],[[0,0],[0]],[[2520,0],[0]],[[0,0],[0]],[[15792,0],[0]],[[0,0],[0]],[[53592,0],[0]],[[0,0],[0]],[[106848,0],[0]],[[0,0],[0]],[[127176,84],[84]],[[0,0],[0]],[[87696,588],[588]],[[0,0],[0]],[[31752,1344],[1344]],[[0,0],[0]],[[4536,1092],[1092]],[[0,0],[0]],[[0,252],[252]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
