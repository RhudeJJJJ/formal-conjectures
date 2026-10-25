/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode030
import Proofs.RadenkovicGutmanD34Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[34],[0]],[[0,0],[0]],[[544,0],[0]],[[0,0],[0]],[[3638,0],[0]],[[0,0],[0]],[[13192,0],[0]],[[0,0],[0]],[[28152,0],[0]],[[0,0],[0]],[[35904,34],[34]],[[0,0],[0]],[[26486,238],[238]],[[0,0],[0]],[[10200,544],[544]],[[0,0],[0]],[[1530,442],[442]],[[0,0],[0]],[[0,102],[102]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
