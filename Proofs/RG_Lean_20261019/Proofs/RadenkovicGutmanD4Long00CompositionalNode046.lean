/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode045
import Proofs.RadenkovicGutmanD4Long00CompositionalNode000
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e046 : NestedArithmetic.Expr 3 := .times e045 e000
noncomputable def p046 : NestedHorner.Poly 3 := [[[]],[[8]]]
theorem step046 : p046=NestedArithmetic.mul p045 p000 := by decide +kernel
#print axioms step046
theorem h046 : NestedArithmetic.compile e046=p046 := StagedExprCompile.compile_times e046 e045 e000 p045 p000 p046 rfl h045 h000 step046
#print axioms h046
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
