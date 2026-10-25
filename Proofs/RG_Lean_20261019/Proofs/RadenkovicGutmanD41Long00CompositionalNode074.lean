/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode065
import Proofs.RadenkovicGutmanD41Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e074 : NestedArithmetic.Expr 3 := .times e065 e057
noncomputable def p074 : NestedHorner.Poly 3 := [[[0],[0]],[[0,123],[123]],[[0,0],[0]],[[1845,533],[533]],[[0,0],[0]],[[12300,656],[656]],[[0,0],[0]],[[31939,287],[287]],[[0,0],[0]],[[43296,41],[41]],[[0]],[[33948]],[[0]],[[15908]],[[0]],[[4387]],[[0]],[[656]],[[0]],[[41]]]
theorem step074 : p074=NestedArithmetic.mul p065 p057 := by decide +kernel
#print axioms step074
theorem h074 : NestedArithmetic.compile e074=p074 := StagedExprCompile.compile_times e074 e065 e057 p065 p057 p074 rfl h065 h057 step074
#print axioms h074
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
