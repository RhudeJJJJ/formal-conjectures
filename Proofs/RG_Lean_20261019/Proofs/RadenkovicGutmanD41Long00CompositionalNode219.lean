/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode065
import Proofs.RadenkovicGutmanD41Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[41],[0]],[[0,0],[0]],[[656,0],[0]],[[0,0],[0]],[[4387,0],[0]],[[0,0],[0]],[[15908,0],[0]],[[0,0],[0]],[[33948,0],[0]],[[0,0],[0]],[[43296,41],[41]],[[0,0],[0]],[[31939,287],[287]],[[0,0],[0]],[[12300,656],[656]],[[0,0],[0]],[[1845,533],[533]],[[0,0],[0]],[[0,123],[123]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
