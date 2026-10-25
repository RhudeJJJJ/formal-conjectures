/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode006
import Proofs.RadenkovicGutmanD39Long00CompositionalNode155
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e180 : NestedArithmetic.Expr 3 := .times e006 e155
noncomputable def p180 : NestedHorner.Poly 3 := [[[1]],[[0]],[[14]],[[0]],[[81]],[[0]],[[250]],[[0]],[[444]],[[0]],[[458]],[[0]],[[265]],[[0]],[[78]],[[0]],[[9]]]
theorem step180 : p180=NestedArithmetic.mul p006 p155 := by decide +kernel
#print axioms step180
theorem h180 : NestedArithmetic.compile e180=p180 := StagedExprCompile.compile_times e180 e006 e155 p006 p155 p180 rfl h006 h155 step180
#print axioms h180
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
