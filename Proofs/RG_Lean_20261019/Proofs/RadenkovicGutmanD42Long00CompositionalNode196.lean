/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode195
import Proofs.RadenkovicGutmanD42Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[168,0],[0]],[[0,0],[0]],[[2520,0],[0]],[[0,0],[0]],[[15792,0],[0]],[[0,0],[0]],[[53592,0],[0]],[[0,0],[0]],[[106848,0],[0]],[[0,0],[0]],[[127176,84],[84]],[[0,0],[0]],[[87696,588],[588]],[[0,0],[0]],[[31752,1344],[1344]],[[0,0],[0]],[[4536,1092],[1092]],[[0,0],[0]],[[0,252],[252]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
