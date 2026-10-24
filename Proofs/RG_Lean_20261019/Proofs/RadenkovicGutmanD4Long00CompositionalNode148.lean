/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode025
import Proofs.RadenkovicGutmanD4Long00CompositionalNode145
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e148 : NestedArithmetic.Expr 3 := .times e025 e145
noncomputable def p148 : NestedHorner.Poly 3 := [[[]],[[0,0]],[[0,0]],[[0,0]],[[0,0]],[[0,0]],[[0,0]],[[0,0]],[[0,0]],[[0,0]],[[0,1]]]
theorem step148 : p148=NestedArithmetic.mul p025 p145 := by decide +kernel
#print axioms step148
theorem h148 : NestedArithmetic.compile e148=p148 := StagedExprCompile.compile_times e148 e025 e145 p025 p145 p148 rfl h025 h145 step148
#print axioms h148
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
