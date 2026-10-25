/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode030
import Proofs.RadenkovicGutmanD41Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[41],[0]],[[0,0],[0]],[[656,0],[0]],[[0,0],[0]],[[4387,0],[0]],[[0,0],[0]],[[15908,0],[0]],[[0,0],[0]],[[33948,0],[0]],[[0,0],[0]],[[43296,41],[41]],[[0,0],[0]],[[31939,287],[287]],[[0,0],[0]],[[12300,656],[656]],[[0,0],[0]],[[1845,533],[533]],[[0,0],[0]],[[0,123],[123]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
