/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode045
import Proofs.RadenkovicGutmanD3Long00StagedUNode006
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e191 : NestedArithmetic.Expr 3 := .times e045 e006
noncomputable def p191 : NestedHorner.Poly 3 := [[[6]]]
theorem step191 : p191=NestedArithmetic.mul p045 p006 := by decide +kernel
#print axioms step191
theorem h191 : NestedArithmetic.compile e191=p191 := StagedExprCompile.compile_times e191 e045 e006 p045 p006 p191 rfl h045 h006 step191
#print axioms h191
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
