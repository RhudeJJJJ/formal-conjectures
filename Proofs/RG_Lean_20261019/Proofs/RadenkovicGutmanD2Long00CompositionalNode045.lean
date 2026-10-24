/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode009
import Proofs.RadenkovicGutmanD2Long00CompositionalNode000
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e009 e000
noncomputable def p045 : NestedHorner.Poly 3 := [[[]],[[4]]]
theorem step045 : p045=NestedArithmetic.mul p009 p000 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e009 e000 p009 p000 p045 rfl h009 h000 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
