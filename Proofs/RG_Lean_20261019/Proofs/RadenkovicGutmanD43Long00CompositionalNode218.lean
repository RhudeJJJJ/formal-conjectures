/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode034
import Proofs.RadenkovicGutmanD43Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-43],[0]],[[0,0],[0]],[[-688,0],[0]],[[0,0],[0]],[[-4601,0],[0]],[[0,0],[0]],[[-16684,0],[0]],[[0,0],[0]],[[-35604,0],[0]],[[0,0],[0]],[[-45408,-43],[-43]],[[0,0],[0]],[[-33497,-301],[-301]],[[0,0],[0]],[[-12900,-688],[-688]],[[0,0],[0]],[[-1935,-559],[-559]],[[0,0],[0]],[[0,-129],[-129]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
