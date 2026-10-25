/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode030
import Proofs.RadenkovicGutmanD41Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[82],[0]],[[0,0],[0]],[[1230,0],[0]],[[0,0],[0]],[[7708,0],[0]],[[0,0],[0]],[[26158,0],[0]],[[0,0],[0]],[[52152,0],[0]],[[0,0],[0]],[[62074,41],[41]],[[0,0],[0]],[[42804,287],[287]],[[0,0],[0]],[[15498,656],[656]],[[0,0],[0]],[[2214,533],[533]],[[0,0],[0]],[[0,123],[123]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
