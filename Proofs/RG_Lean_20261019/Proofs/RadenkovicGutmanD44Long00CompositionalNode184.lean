/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode030
import Proofs.RadenkovicGutmanD44Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[44],[0]],[[0,0],[0]],[[704,0],[0]],[[0,0],[0]],[[4708,0],[0]],[[0,0],[0]],[[17072,0],[0]],[[0,0],[0]],[[36432,0],[0]],[[0,0],[0]],[[46464,44],[44]],[[0,0],[0]],[[34276,308],[308]],[[0,0],[0]],[[13200,704],[704]],[[0,0],[0]],[[1980,572],[572]],[[0,0],[0]],[[0,132],[132]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
