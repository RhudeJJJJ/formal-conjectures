/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode030
import Proofs.RadenkovicGutmanD12Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[12],[0]],[[0,0],[0]],[[192,0],[0]],[[0,0],[0]],[[1284,0],[0]],[[0,0],[0]],[[4656,0],[0]],[[0,0],[0]],[[9936,0],[0]],[[0,0],[0]],[[12672,12],[12]],[[0,0],[0]],[[9348,84],[84]],[[0,0],[0]],[[3600,192],[192]],[[0,0],[0]],[[540,156],[156]],[[0,0],[0]],[[0,36],[36]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
