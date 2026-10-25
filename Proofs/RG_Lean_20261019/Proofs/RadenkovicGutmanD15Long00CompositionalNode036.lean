/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode017
import Proofs.RadenkovicGutmanD15Long00CompositionalNode000
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e036 : NestedArithmetic.Expr 3 := .times e017 e000
noncomputable def p036 : NestedHorner.Poly 3 := [[[]],[[2]]]
theorem step036 : p036=NestedArithmetic.mul p017 p000 := by decide +kernel
#print axioms step036
theorem h036 : NestedArithmetic.compile e036=p036 := StagedExprCompile.compile_times e036 e017 e000 p017 p000 p036 rfl h017 h000 step036
#print axioms h036
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
