/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode155
import Proofs.RadenkovicGutmanD10Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e175 : NestedArithmetic.Expr 3 := .times e155 e003
noncomputable def p175 : NestedHorner.Poly 3 := [[[]],[[0]],[[1]],[[0]],[[14]],[[0]],[[81]],[[0]],[[250]],[[0]],[[444]],[[0]],[[458]],[[0]],[[265]],[[0]],[[78]],[[0]],[[9]]]
theorem step175 : p175=NestedArithmetic.mul p155 p003 := by decide +kernel
#print axioms step175
theorem h175 : NestedArithmetic.compile e175=p175 := StagedExprCompile.compile_times e175 e155 e003 p155 p003 p175 rfl h155 h003 step175
#print axioms h175
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
