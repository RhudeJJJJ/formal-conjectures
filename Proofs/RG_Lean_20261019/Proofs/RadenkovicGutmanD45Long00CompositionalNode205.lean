/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode204
import Proofs.RadenkovicGutmanD45Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[90,0],[0]],[[0,0],[0]],[[1440,0],[0]],[[0,0],[0]],[[9630,0],[0]],[[0,0],[0]],[[34920,0],[0]],[[0,0],[0]],[[74520,0],[0]],[[0,0],[0]],[[95040,90],[90]],[[0,0],[0]],[[70110,630],[630]],[[0,0],[0]],[[27000,1440],[1440]],[[0,0],[0]],[[4050,1170],[1170]],[[0,0],[0]],[[0,270],[270]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
