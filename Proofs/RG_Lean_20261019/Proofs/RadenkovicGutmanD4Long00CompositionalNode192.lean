/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode045
import Proofs.RadenkovicGutmanD4Long00CompositionalNode006
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e045 e006
noncomputable def p192 : NestedHorner.Poly 3 := [[[8]]]
theorem step192 : p192=NestedArithmetic.mul p045 p006 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e045 e006 p045 p006 p192 rfl h045 h006 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
