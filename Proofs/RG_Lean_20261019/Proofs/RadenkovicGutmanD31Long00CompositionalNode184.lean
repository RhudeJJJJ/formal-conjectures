/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode030
import Proofs.RadenkovicGutmanD31Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[31],[0]],[[0,0],[0]],[[496,0],[0]],[[0,0],[0]],[[3317,0],[0]],[[0,0],[0]],[[12028,0],[0]],[[0,0],[0]],[[25668,0],[0]],[[0,0],[0]],[[32736,31],[31]],[[0,0],[0]],[[24149,217],[217]],[[0,0],[0]],[[9300,496],[496]],[[0,0],[0]],[[1395,403],[403]],[[0,0],[0]],[[0,93],[93]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
