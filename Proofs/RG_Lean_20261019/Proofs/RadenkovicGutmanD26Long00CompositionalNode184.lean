/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode030
import Proofs.RadenkovicGutmanD26Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[26],[0]],[[0,0],[0]],[[416,0],[0]],[[0,0],[0]],[[2782,0],[0]],[[0,0],[0]],[[10088,0],[0]],[[0,0],[0]],[[21528,0],[0]],[[0,0],[0]],[[27456,26],[26]],[[0,0],[0]],[[20254,182],[182]],[[0,0],[0]],[[7800,416],[416]],[[0,0],[0]],[[1170,338],[338]],[[0,0],[0]],[[0,78],[78]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
