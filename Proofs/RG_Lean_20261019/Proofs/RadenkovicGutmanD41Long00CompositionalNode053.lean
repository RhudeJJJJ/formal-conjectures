/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode030
import Proofs.RadenkovicGutmanD41Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,41]],[[0,0],[0]],[[369,369],[369]],[[0,0],[0]],[[6519,984],[984]],[[0,0],[0]],[[28577,902],[902]],[[0,0],[0]],[[58630,328],[328]],[[0,0],[0]],[[67404,41],[41]],[[0]],[[46576]],[[0]],[[19721]],[[0]],[[5002]],[[0]],[[697]],[[0]],[[41]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
