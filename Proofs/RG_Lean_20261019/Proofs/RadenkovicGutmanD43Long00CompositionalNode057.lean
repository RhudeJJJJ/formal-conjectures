/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode034
import Proofs.RadenkovicGutmanD43Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-129],[-129]],[[0,0],[0]],[[-1935,-559],[-559]],[[0,0],[0]],[[-12900,-688],[-688]],[[0,0],[0]],[[-33497,-301],[-301]],[[0,0],[0]],[[-45408,-43],[-43]],[[0]],[[-35604]],[[0]],[[-16684]],[[0]],[[-4601]],[[0]],[[-688]],[[0]],[[-43]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
