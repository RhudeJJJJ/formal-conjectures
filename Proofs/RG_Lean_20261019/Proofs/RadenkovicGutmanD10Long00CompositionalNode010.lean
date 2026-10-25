/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode009
import Proofs.RadenkovicGutmanD10Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e010 : NestedArithmetic.Expr 3 := .times e009 e003
noncomputable def p010 : NestedHorner.Poly 3 := [[[]],[[0]],[[4]]]
theorem step010 : p010=NestedArithmetic.mul p009 p003 := by decide +kernel
#print axioms step010
theorem h010 : NestedArithmetic.compile e010=p010 := StagedExprCompile.compile_times e010 e009 e003 p009 p003 p010 rfl h009 h003 step010
#print axioms h010
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
