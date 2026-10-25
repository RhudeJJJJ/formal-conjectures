/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode025
import Proofs.RadenkovicGutmanD35Long00CompositionalNode146
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e149 : NestedArithmetic.Expr 3 := .times e025 e146
noncomputable def p149 : NestedHorner.Poly 3 := [[[]],[[0,0]],[[0,0]],[[0,0]],[[0,0]],[[0,0]],[[0,0]],[[0,0]],[[0,0]],[[0,0]],[[0,1]]]
theorem step149 : p149=NestedArithmetic.mul p025 p146 := by decide +kernel
#print axioms step149
theorem h149 : NestedArithmetic.compile e149=p149 := StagedExprCompile.compile_times e149 e025 e146 p025 p146 p149 rfl h025 h146 step149
#print axioms h149
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
