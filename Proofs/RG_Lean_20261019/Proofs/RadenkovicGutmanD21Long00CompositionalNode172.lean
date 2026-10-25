/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode171
import Proofs.RadenkovicGutmanD21Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[42,0],[0]],[[0,0],[0]],[[630,0],[0]],[[0,0],[0]],[[3948,0],[0]],[[0,0],[0]],[[13398,0],[0]],[[0,0],[0]],[[26712,0],[0]],[[0,0],[0]],[[31794,21],[21]],[[0,0],[0]],[[21924,147],[147]],[[0,0],[0]],[[7938,336],[336]],[[0,0],[0]],[[1134,273],[273]],[[0,0],[0]],[[0,63],[63]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
