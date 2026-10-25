/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode034
import Proofs.RadenkovicGutmanD43Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-86],[0]],[[0,0],[0]],[[-1290,0],[0]],[[0,0],[0]],[[-8084,0],[0]],[[0,0],[0]],[[-27434,0],[0]],[[0,0],[0]],[[-54696,0],[0]],[[0,0],[0]],[[-65102,-43],[-43]],[[0,0],[0]],[[-44892,-301],[-301]],[[0,0],[0]],[[-16254,-688],[-688]],[[0,0],[0]],[[-2322,-559],[-559]],[[0,0],[0]],[[0,-129],[-129]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
