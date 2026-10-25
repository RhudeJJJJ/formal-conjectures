/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode002
import Proofs.RadenkovicGutmanD13Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e004 : NestedArithmetic.Expr 3 := .times e002 e003
noncomputable def p004 : NestedHorner.Poly 3 := [[[]],[[0]],[[3]]]
theorem step004 : p004=NestedArithmetic.mul p002 p003 := by decide +kernel
#print axioms step004
theorem h004 : NestedArithmetic.compile e004=p004 := StagedExprCompile.compile_times e004 e002 e003 p002 p003 p004 rfl h002 h003 step004
#print axioms h004
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
