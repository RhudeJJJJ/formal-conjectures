/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode030
import Proofs.RadenkovicGutmanD10Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[10],[0]],[[0,0],[0]],[[160,0],[0]],[[0,0],[0]],[[1070,0],[0]],[[0,0],[0]],[[3880,0],[0]],[[0,0],[0]],[[8280,0],[0]],[[0,0],[0]],[[10560,10],[10]],[[0,0],[0]],[[7790,70],[70]],[[0,0],[0]],[[3000,160],[160]],[[0,0],[0]],[[450,130],[130]],[[0,0],[0]],[[0,30],[30]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
