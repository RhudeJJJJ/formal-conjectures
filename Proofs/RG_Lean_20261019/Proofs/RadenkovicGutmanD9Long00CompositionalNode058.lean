/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode036
import Proofs.RadenkovicGutmanD9Long00CompositionalNode037
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e058 : NestedArithmetic.Expr 3 := .times e036 e037
noncomputable def p058 : NestedHorner.Poly 3 := [[[]],[[-14]]]
theorem step058 : p058=NestedArithmetic.mul p036 p037 := by decide +kernel
#print axioms step058
theorem h058 : NestedArithmetic.compile e058=p058 := StagedExprCompile.compile_times e058 e036 e037 p036 p037 p058 rfl h036 h037 step058
#print axioms h058
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
