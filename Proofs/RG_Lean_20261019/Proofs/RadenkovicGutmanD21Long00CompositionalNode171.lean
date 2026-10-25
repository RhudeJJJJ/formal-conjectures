/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode030
import Proofs.RadenkovicGutmanD21Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[42],[0]],[[0,0],[0]],[[630,0],[0]],[[0,0],[0]],[[3948,0],[0]],[[0,0],[0]],[[13398,0],[0]],[[0,0],[0]],[[26712,0],[0]],[[0,0],[0]],[[31794,21],[21]],[[0,0],[0]],[[21924,147],[147]],[[0,0],[0]],[[7938,336],[336]],[[0,0],[0]],[[1134,273],[273]],[[0,0],[0]],[[0,63],[63]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
