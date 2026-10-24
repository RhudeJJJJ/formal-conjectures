/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode118
import Proofs.RadenkovicGutmanD4Long00CompositionalNode036
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .times e118 e036
noncomputable def p173 : NestedHorner.Poly 3 := [[[-4]]]
theorem step173 : p173=NestedArithmetic.mul p118 p036 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_times e173 e118 e036 p118 p036 p173 rfl h118 h036 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
