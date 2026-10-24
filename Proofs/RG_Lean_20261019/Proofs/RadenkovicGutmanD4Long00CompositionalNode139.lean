/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode138
import Proofs.RadenkovicGutmanD4Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e139 : NestedArithmetic.Expr 3 := .times e138 e003
noncomputable def p139 : NestedHorner.Poly 3 := [[[]],[[0]],[[2]]]
theorem step139 : p139=NestedArithmetic.mul p138 p003 := by decide +kernel
#print axioms step139
theorem h139 : NestedArithmetic.compile e139=p139 := StagedExprCompile.compile_times e139 e138 e003 p138 p003 p139 rfl h138 h003 step139
#print axioms h139
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
