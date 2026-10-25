/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode030
import Proofs.RadenkovicGutmanD14Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[14],[0]],[[0,0],[0]],[[224,0],[0]],[[0,0],[0]],[[1498,0],[0]],[[0,0],[0]],[[5432,0],[0]],[[0,0],[0]],[[11592,0],[0]],[[0,0],[0]],[[14784,14],[14]],[[0,0],[0]],[[10906,98],[98]],[[0,0],[0]],[[4200,224],[224]],[[0,0],[0]],[[630,182],[182]],[[0,0],[0]],[[0,42],[42]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
