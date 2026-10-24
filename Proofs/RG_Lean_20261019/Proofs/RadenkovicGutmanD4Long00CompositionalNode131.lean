/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode130
import Proofs.RadenkovicGutmanD4Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e131 : NestedArithmetic.Expr 3 := .times e130 e003
noncomputable def p131 : NestedHorner.Poly 3 := [[[]],[[0]],[[4]]]
theorem step131 : p131=NestedArithmetic.mul p130 p003 := by decide +kernel
#print axioms step131
theorem h131 : NestedArithmetic.compile e131=p131 := StagedExprCompile.compile_times e131 e130 e003 p130 p003 p131 rfl h130 h003 step131
#print axioms h131
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
