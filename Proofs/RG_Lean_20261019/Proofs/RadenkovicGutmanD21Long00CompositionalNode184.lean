/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode030
import Proofs.RadenkovicGutmanD21Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[21],[0]],[[0,0],[0]],[[336,0],[0]],[[0,0],[0]],[[2247,0],[0]],[[0,0],[0]],[[8148,0],[0]],[[0,0],[0]],[[17388,0],[0]],[[0,0],[0]],[[22176,21],[21]],[[0,0],[0]],[[16359,147],[147]],[[0,0],[0]],[[6300,336],[336]],[[0,0],[0]],[[945,273],[273]],[[0,0],[0]],[[0,63],[63]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
